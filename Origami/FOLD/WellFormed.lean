import Origami.FOLD.Properties

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
