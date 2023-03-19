include "cpw.mm"
include "chmph.mm"
include "wbr.mm"
include "wss.mm"
include "cuni.mm"
include "pwuni.mm"
include "pweqi.mm"
include "sseqtr4i.mm"
include "a1i.mm"
include "chmeo.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "hmph.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "n0.mm"
include "elpwi.mm"
include "wa.mm"
include "cima.mm"
include "crn.mm"
include "imassrn.mm"
include "wf1o.mm"
include "wf.mm"
include "unipw.mm"
include "eqcomi.mm"
include "hmeof1o.mm"
include "f1of.mm"
include "frn.mm"
include "3syl.mm"
include "adantr.mm"
include "syl5ss.mm"
include "vex.mm"
include "imaex.mm"
include "elpw.mm"
include "sylibr.mm"
include "hmeoopn.mm"
include "mpbird.mm"
include "ex.mm"
include "syl5.mm"
include "ssrdv.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "eqssd.mm"

theorem hmphdis
  let cA: class A
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  assume hmphdis.1: |- X = U. J


  assert |- ( J ~= ~P A -> J = ~P X )

  proof
    cJ
    cA
    cpw
    #
    chmph
    wbr
    #
    cJ
    cX
    cpw
    #
    cJ
    @2
    wss
    @1
    cJ
    cJ
    cuni
    #
    cpw
    @2
    cJ
    pwuni
    cX
    @3
    hmphdis.1
    pweqi
    sseqtr4i
    a1i
    @1
    cJ
    @0
    chmeo
    co
    #
    c0
    wne
    #
    @2
    cJ
    wss
    #
    cJ
    @0
    hmph
    @5
    vf
    cv
    #
    @4
    wcel
    #
    vf
    wex
    @6
    vf
    @4
    n0
    @8
    @6
    vf
    @8
    vx
    @2
    cJ
    vx
    cv
    #
    @2
    wcel
    @9
    cX
    wss
    #
    @8
    @9
    cJ
    wcel
    #
    @9
    cX
    elpwi
    @8
    @10
    @11
    @8
    @10
    wa
    #
    @11
    @7
    @9
    cima
    #
    @0
    wcel
    #
    @12
    @13
    cA
    wss
    @14
    @12
    @13
    @7
    crn
    #
    cA
    @7
    @9
    imassrn
    @8
    @15
    cA
    wss
    #
    @10
    @8
    cX
    cA
    @7
    wf1o
    cX
    cA
    @7
    wf
    @16
    @7
    cJ
    @0
    cX
    cA
    hmphdis.1
    @0
    cuni
    cA
    cA
    unipw
    eqcomi
    hmeof1o
    cX
    cA
    @7
    f1of
    cX
    cA
    @7
    frn
    3syl
    adantr
    syl5ss
    @13
    cA
    @7
    @9
    vf
    vex
    imaex
    elpw
    sylibr
    @9
    @7
    cJ
    @0
    cX
    hmphdis.1
    hmeoopn
    mpbird
    ex
    syl5
    ssrdv
    exlimiv
    sylbi
    sylbi
    eqssd
end
