include "wcel.mm"
include "cpw.mm"
include "c0.mm"
include "cv.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "wa.mm"
include "cuni.mm"
include "wi.mm"
include "w3a.mm"
include "cvv.mm"
include "pwexg.mm"
include "pwidg.mm"
include "syl.mm"
include "0elpw.mm"
include "a1i.mm"
include "adantr.mm"
include "elpwdifcl.mm"
include "ralrimiva.mm"
include "wss.mm"
include "elpwi.mm"
include "pwuniss.mm"
include "adantl.mm"
include "vuniex.mm"
include "elpw.mm"
include "sylibr.mm"
include "ex.mm"
include "3jca.mm"
include "jca.mm"
include "isldsys.mm"

theorem pwldsys
  let vx: setvar x
  let vy: setvar y
  let cL: class L
  let cO: class O
  let cV: class V
  let vs: setvar s
  let vu: setvar u
  let vt: setvar t
  let cS: class S
  assume isldsys.l: |- L = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s ( O \ x ) e. s /\ A. x e. ~P s ( ( x ~<_ _om /\ Disj_ y e. x y ) -> U. x e. s ) ) }

  disjoint s y
  disjoint O s
  disjoint O x
  disjoint s x
  disjoint V x
  disjoint s u
  disjoint u y
  disjoint L t
  disjoint O t
  disjoint s t
  disjoint t x
  disjoint S s
  disjoint S x
  assert |- ( O e. V -> ~P O e. L )

  proof
    cO
    cV
    wcel
    #
    cO
    cpw
    #
    @1
    cpw
    #
    wcel
    #
    c0
    @1
    wcel
    #
    cO
    vx
    cv
    #
    cdif
    @1
    wcel
    #
    vx
    @1
    wral
    #
    @5
    com
    cdom
    wbr
    vy
    @5
    vy
    cv
    wdisj
    wa
    #
    @5
    cuni
    #
    @1
    wcel
    #
    wi
    #
    vx
    @2
    wral
    #
    w3a
    #
    wa
    @1
    cL
    wcel
    @0
    @3
    @13
    @0
    @1
    cvv
    wcel
    @3
    cO
    cV
    pwexg
    @1
    cvv
    pwidg
    syl
    @0
    @4
    @7
    @12
    @4
    @0
    cO
    0elpw
    a1i
    @0
    @6
    vx
    @1
    @0
    @5
    @1
    wcel
    #
    wa
    cO
    @5
    cO
    @0
    cO
    @1
    wcel
    @14
    cO
    cV
    pwidg
    adantr
    elpwdifcl
    ralrimiva
    @0
    @11
    vx
    @2
    @0
    @5
    @2
    wcel
    #
    wa
    #
    @8
    @10
    @16
    @10
    @8
    @16
    @9
    cO
    wss
    #
    @10
    @15
    @17
    @0
    @15
    @5
    @1
    wss
    @17
    @5
    @1
    elpwi
    @5
    cO
    pwuniss
    syl
    adantl
    @9
    cO
    vx
    vuniex
    elpw
    sylibr
    adantr
    ex
    ralrimiva
    3jca
    jca
    vx
    vy
    @1
    cL
    cO
    vs
    isldsys.l
    isldsys
    sylibr
end
