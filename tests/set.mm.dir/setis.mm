include "wcel.mm"
include "cab.mm"
include "cv.mm"
include "wral.mm"
include "cfv.mm"
include "wi.mm"
include "wal.mm"
include "wss.mm"
include "ssabral.mm"
include "imbi12i.mm"
include "albii.mm"
include "sylibr.mm"
include "setrec2v.mm"
include "sseld.mm"
include "elabg.mm"
include "mpbidi.mm"

theorem setis
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let cA: class A
  let cB: class B
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vx: setvar x
  assume setis.1: |- B = setrecs ( F )
  assume setis.2: |- ( b = A -> ( ps <-> ch ) )
  assume setis.3: |- ( ph -> A. a ( A. b e. a ps -> A. b e. ( F ` a ) ps ) )

  disjoint F a
  disjoint F b
  disjoint a b
  disjoint a ps
  disjoint b ch
  disjoint A b
  disjoint k x
  assert |- ( ph -> ( A e. B -> ch ) )

  proof
    cA
    cB
    wcel
    cA
    wps
    vb
    cab
    #
    wcel
    wch
    wph
    wph
    cB
    @0
    cA
    wph
    cB
    @0
    cF
    va
    setis.1
    wph
    wps
    vb
    va
    cv
    #
    wral
    #
    wps
    vb
    @1
    cF
    cfv
    #
    wral
    #
    wi
    #
    va
    wal
    @1
    @0
    wss
    #
    @3
    @0
    wss
    #
    wi
    #
    va
    wal
    setis.3
    @8
    @5
    va
    @6
    @2
    @7
    @4
    wps
    vb
    @1
    ssabral
    wps
    vb
    @3
    ssabral
    imbi12i
    albii
    sylibr
    setrec2v
    sseld
    wps
    wch
    vb
    cA
    cB
    setis.2
    elabg
    mpbidi
end
