include "cuni.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "wrex.mm"
include "wss.mm"
include "cpred.mm"
include "ciun.mm"
include "dmuni.mm"
include "eleq2i.mm"
include "eliun.mm"
include "bitri.mm"
include "wa.mm"
include "wi.mm"
include "ssel2.mm"
include "wfn.mm"
include "wral.mm"
include "cfv.mm"
include "cres.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "wex.mm"
include "frrlem1.mm"
include "abeq2i.mm"
include "predeq3.mm"
include "sseq1d.mm"
include "rspccv.mm"
include "ad2antlr.mm"
include "fndm.mm"
include "eleq2d.mm"
include "sseq2d.mm"
include "imbi12d.mm"
include "syl5ibr.mm"
include "3impib.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "syl.mm"
include "weq.mm"
include "dmeq.mm"
include "rspcev.mm"
include "ssiun.mm"
include "syl6sseqr.mm"
include "ex.mm"
include "adantl.mm"
include "syld.mm"
include "rexlimdva.mm"
include "syl5bi.mm"

theorem frrlem5e
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vf: setvar f
  let cG: class G
  let cX: class X
  let vt: setvar t
  let vw: setvar w
  let vz: setvar z
  let vg: setvar g
  let vh: setvar h
  let vu: setvar u
  let vv: setvar v
  let va: setvar a
  assume frrlem5.1: |- R Fr A
  assume frrlem5.2: |- R Se A
  assume frrlem5.3: |- B = { f | E. x ( f Fn x /\ ( x C_ A /\ A. y e. x Pred ( R , A , y ) C_ x ) /\ A. y e. x ( f ` y ) = ( y G ( f |` Pred ( R , A , y ) ) ) ) }

  disjoint x y
  disjoint A f
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint f x
  disjoint f y
  disjoint G f
  disjoint G x
  disjoint G y
  disjoint R f
  disjoint R x
  disjoint R y
  disjoint B x
  disjoint A t
  disjoint A w
  disjoint A z
  disjoint t w
  disjoint t z
  disjoint w z
  disjoint f t
  disjoint f w
  disjoint f z
  disjoint G t
  disjoint G w
  disjoint G z
  disjoint R t
  disjoint R w
  disjoint R z
  disjoint t x
  disjoint w x
  disjoint x z
  disjoint t y
  disjoint w y
  disjoint y z
  disjoint X t
  disjoint X w
  disjoint X z
  disjoint C w
  disjoint A g
  disjoint f g
  disjoint A h
  disjoint h x
  disjoint h y
  disjoint f h
  disjoint G h
  disjoint G g
  disjoint g u
  disjoint u v
  disjoint u x
  disjoint g v
  disjoint g x
  disjoint v x
  disjoint g y
  disjoint h u
  disjoint h v
  disjoint R g
  disjoint R h
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint f z
  disjoint G z
  disjoint R z
  disjoint x z
  disjoint y z
  disjoint C g
  disjoint B g
  disjoint B h
  disjoint B u
  disjoint B v
  disjoint g h
  disjoint A a
  disjoint a f
  disjoint a h
  disjoint a x
  disjoint a y
  disjoint a g
  disjoint B a
  disjoint G a
  disjoint R a
  assert |- ( C C_ B -> ( X e. dom U. C -> Pred ( R , A , X ) C_ dom U. C ) )

  proof
    cX
    cC
    cuni
    cdm
    #
    wcel
    #
    cX
    vz
    cv
    #
    cdm
    #
    wcel
    #
    vz
    cC
    wrex
    #
    cC
    cB
    wss
    #
    cA
    cR
    cX
    cpred
    #
    @0
    wss
    #
    @1
    cX
    vz
    cC
    @3
    ciun
    #
    wcel
    @5
    @0
    @9
    cX
    vz
    cC
    dmuni
    eleq2i
    vz
    cX
    cC
    @3
    eliun
    bitri
    @6
    @4
    @8
    vz
    cC
    @6
    @2
    cC
    wcel
    #
    wa
    #
    @4
    @7
    @3
    wss
    #
    @8
    @11
    @2
    cB
    wcel
    #
    @4
    @12
    wi
    #
    cC
    cB
    @2
    ssel2
    @13
    @2
    vw
    cv
    #
    wfn
    #
    @15
    cA
    wss
    #
    cA
    cR
    vt
    cv
    #
    cpred
    #
    @15
    wss
    #
    vt
    @15
    wral
    #
    wa
    #
    @18
    @2
    cfv
    @18
    @2
    @19
    cres
    cG
    co
    wceq
    vt
    @15
    wral
    #
    w3a
    #
    vw
    wex
    #
    @14
    @25
    vz
    cB
    vx
    vy
    vw
    vt
    cA
    cB
    cR
    vf
    vz
    cG
    frrlem5.3
    frrlem1
    abeq2i
    @24
    @14
    vw
    @16
    @22
    @23
    @14
    @22
    @23
    wa
    @14
    @16
    cX
    @15
    wcel
    #
    @7
    @15
    wss
    #
    wi
    #
    @21
    @28
    @17
    @23
    @20
    @27
    vt
    cX
    @15
    @18
    cX
    wceq
    @19
    @7
    @15
    cA
    cR
    @18
    cX
    predeq3
    sseq1d
    rspccv
    ad2antlr
    @16
    @4
    @26
    @12
    @27
    @16
    @3
    @15
    cX
    @15
    @2
    fndm
    #
    eleq2d
    @16
    @3
    @15
    @7
    @29
    sseq2d
    imbi12d
    syl5ibr
    3impib
    exlimiv
    sylbi
    syl
    @10
    @12
    @8
    wi
    @6
    @10
    @12
    @8
    @10
    @12
    wa
    #
    @7
    vw
    cC
    @15
    cdm
    #
    ciun
    #
    @0
    @30
    @7
    @31
    wss
    #
    vw
    cC
    wrex
    @7
    @32
    wss
    @33
    @12
    vw
    @2
    cC
    vw
    vz
    weq
    @31
    @3
    @7
    @15
    @2
    dmeq
    sseq2d
    rspcev
    vw
    cC
    @31
    @7
    ssiun
    syl
    vw
    cC
    dmuni
    syl6sseqr
    ex
    adantl
    syld
    rexlimdva
    syl5bi
end
