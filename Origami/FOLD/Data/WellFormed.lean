import Origami.FOLD.Data.Properties

/-- Index validity -/
def EdgeWellIndexed (F : Fold) (e : Edge) : Prop :=
  e.u < F.vertices.length ∧
  e.v < F.vertices.length

def FaceWellIndexed (F : Fold) (f : Face) : Prop :=
  ∀ v ∈ f.verts, v < F.vertices.length


def EdgesWellIndexed (F : Fold) : Prop :=
  ∀ e ∈ F.edges, EdgeWellIndexed F e

def FacesWellIndexed (F : Fold) : Prop :=
  ∀ f ∈ F.faces, FaceWellIndexed F f


/-- Structural constraints -/
def NoDegenerateEdges (F : Fold) : Prop :=
  ∀ e ∈ F.edges, e.u ≠ e.v

def FacesHaveSizeGE3 (F : Fold) : Prop :=
  ∀ f ∈ F.faces, 3 ≤ f.verts.length

def FacesNoDuplicates (F : Fold) : Prop :=
  ∀ f ∈ F.faces, f.verts.Nodup


/-- Dimension consistency -/
def SameDimension (F : Fold) : Prop :=
  ∀ v1 ∈ F.vertices, ∀ v2 ∈ F.vertices,
    v1.coords.length = v2.coords.length


/-- Full well-formedness (data level only) -/
def WellFormed (F : Fold) : Prop :=
  EdgesWellIndexed F ∧
  FacesWellIndexed F ∧
  SameDimension F ∧
  FacesHaveSizeGE3 F ∧
  NoDegenerateEdges F ∧
  FacesNoDuplicates F

/-- Extract `EdgesWellIndexed` from `WellFormed`. -/
lemma wellFormed_edgesWellIndexed {F : Fold} (h : WellFormed F) : EdgesWellIndexed F :=
  h.1

/-- Extract `FacesWellIndexed` from `WellFormed`. -/
lemma wellFormed_facesWellIndexed {F : Fold} (h : WellFormed F) : FacesWellIndexed F :=
  h.2.1

/-- Extract `SameDimension` from `WellFormed`. -/
lemma wellFormed_sameDimension {F : Fold} (h : WellFormed F) : SameDimension F :=
  h.2.2.1

/-- Unpack the left index bound from `EdgeWellIndexed`. -/
lemma edgeWellIndexed_u_lt {F : Fold} {e : Edge} (h : EdgeWellIndexed F e) :
    e.u < F.vertices.length :=
  h.1

/-- Unpack the right index bound from `EdgeWellIndexed`. -/
lemma edgeWellIndexed_v_lt {F : Fold} {e : Edge} (h : EdgeWellIndexed F e) :
    e.v < F.vertices.length :=
  h.2

/-- Any edge listed in a well-formed fold is index-valid. -/
lemma edgeWellIndexed_of_mem_wellFormed {F : Fold} (hWF : WellFormed F) {e : Edge}
    (he : e ∈ F.edges) : EdgeWellIndexed F e :=
  (wellFormed_edgesWellIndexed hWF) e he
