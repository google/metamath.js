include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "cfv.mm"
include "wa.mm"
include "wn.mm"
include "wal.mm"
include "wex.mm"
include "csn.mm"
include "cdif.mm"
include "ssdifsn.mm"
include "simprbi.mm"
include "con2i.mm"
include "wi.mm"
include "wceq.mm"
include "sseq1.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "notbid.mm"
include "spv.mm"
include "imnan.mm"
include "idd.mm"
include "cvv.mm"
include "vex.mm"
include "a1i.mm"
include "id.mm"
include "setrec1.mm"
include "jctild.mm"
include "a2i.mm"
include "sylbir.mm"
include "adantrd.mm"
include "3imtr4g.mm"
include "syl.mm"
include "alrimiv.mm"
include "setrec2v.mm"
include "nsyl.mm"
include "df-ex.mm"
include "sylibr.mm"

theorem elsetrecslem
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let va: setvar a
  let vk: setvar k
  assume elsetrecs.1: |- B = setrecs ( F )

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint A a
  disjoint a x
  disjoint B a
  disjoint F a
  disjoint k x
  assert |- ( A e. B -> E. x ( x C_ B /\ A e. ( F ` x ) ) )

  proof
    cA
    cB
    wcel
    #
    vx
    cv
    #
    cB
    wss
    #
    cA
    @1
    cF
    cfv
    #
    wcel
    #
    wa
    #
    wn
    #
    vx
    wal
    #
    wn
    @5
    vx
    wex
    @0
    cB
    cB
    cA
    csn
    cdif
    #
    wss
    #
    @7
    @9
    @0
    @9
    cB
    cB
    wss
    @0
    wn
    cB
    cB
    cA
    ssdifsn
    simprbi
    con2i
    @7
    cB
    @8
    cF
    va
    elsetrecs.1
    @7
    va
    cv
    #
    @8
    wss
    #
    @10
    cF
    cfv
    #
    @8
    wss
    #
    wi
    #
    va
    @7
    @10
    cB
    wss
    #
    cA
    @12
    wcel
    #
    wa
    #
    wn
    #
    @14
    @6
    @18
    vx
    va
    @1
    @10
    wceq
    #
    @5
    @17
    @19
    @2
    @15
    @4
    @16
    @1
    @10
    cB
    sseq1
    @19
    @3
    @12
    cA
    @1
    @10
    cF
    fveq2
    eleq2d
    anbi12d
    notbid
    spv
    @18
    @15
    cA
    @10
    wcel
    wn
    #
    wa
    @12
    cB
    wss
    #
    @16
    wn
    #
    wa
    #
    @11
    @13
    @18
    @15
    @23
    @20
    @18
    @15
    @22
    wi
    @15
    @23
    wi
    @15
    @16
    imnan
    @15
    @22
    @23
    @15
    @22
    @22
    @21
    @15
    @22
    idd
    @15
    @10
    cB
    cF
    elsetrecs.1
    @10
    cvv
    wcel
    @15
    va
    vex
    a1i
    @15
    id
    setrec1
    jctild
    a2i
    sylbir
    adantrd
    @10
    cB
    cA
    ssdifsn
    @12
    cB
    cA
    ssdifsn
    3imtr4g
    syl
    alrimiv
    setrec2v
    nsyl
    @5
    vx
    df-ex
    sylibr
end
