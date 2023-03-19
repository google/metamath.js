include "cpw.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cress.mm"
include "co.mm"
include "clss.mm"
include "cfv.mm"
include "chlt.mm"
include "lcdval2.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "clmod.mm"
include "wb.mm"
include "dvhlmod.mm"
include "lduallmod.mm"
include "lclkr.mm"
include "eqid.mm"
include "lsslss.mm"
include "syl2anc.mm"
include "bitrd.mm"
include "elin.mm"
include "selpw.mm"
include "anbi2i.mm"
include "bitr2i.mm"
include "syl6bb.mm"
include "eqrdv.mm"

theorem lcdlss
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let cO: class O
  let cW: class W
  let vu: setvar u
  assume lcdlss.h: |- H = ( LHyp ` K )
  assume lcdlss.o: |- O = ( ( ocH ` K ) ` W )
  assume lcdlss.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdlss.s: |- S = ( LSubSp ` C )
  assume lcdlss.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdlss.f: |- F = ( LFnl ` U )
  assume lcdlss.l: |- L = ( LKer ` U )
  assume lcdlss.d: |- D = ( LDual ` U )
  assume lcdlss.t: |- T = ( LSubSp ` D )
  assume lcdlss.b: |- B = { f e. F | ( O ` ( O ` ( L ` f ) ) ) = ( L ` f ) }
  assume lcdlss.k: |- ( ph -> ( K e. HL /\ W e. H ) )

  disjoint D f
  disjoint F f
  disjoint K f
  disjoint L f
  disjoint O f
  disjoint U f
  disjoint W f
  disjoint B u
  disjoint S u
  disjoint T u
  disjoint ph u
  assert |- ( ph -> S = ( T i^i ~P B ) )

  proof
    wph
    vu
    cS
    cT
    cB
    cpw
    #
    cin
    #
    wph
    vu
    cv
    #
    cS
    wcel
    #
    @2
    cT
    wcel
    #
    @2
    cB
    wss
    #
    wa
    #
    @2
    @1
    wcel
    #
    wph
    @3
    @2
    cD
    cB
    cress
    co
    #
    clss
    cfv
    #
    wcel
    #
    @6
    wph
    cS
    @9
    @2
    wph
    cS
    cC
    clss
    cfv
    @9
    lcdlss.s
    wph
    cC
    @8
    clss
    wph
    cB
    cC
    cD
    cU
    vf
    cF
    cH
    cK
    cL
    cO
    cW
    chlt
    lcdlss.h
    lcdlss.o
    lcdlss.c
    lcdlss.u
    lcdlss.f
    lcdlss.l
    lcdlss.d
    lcdlss.k
    lcdlss.b
    lcdval2
    fveq2d
    syl5eq
    eleq2d
    wph
    cD
    clmod
    wcel
    cB
    cT
    wcel
    @10
    @6
    wb
    wph
    cD
    cU
    lcdlss.d
    wph
    cU
    cH
    cK
    cW
    lcdlss.h
    lcdlss.u
    lcdlss.k
    dvhlmod
    lduallmod
    wph
    cB
    cD
    cT
    cU
    vf
    cF
    cH
    cK
    cL
    cO
    cW
    lcdlss.h
    lcdlss.u
    lcdlss.o
    lcdlss.f
    lcdlss.l
    lcdlss.d
    lcdlss.t
    lcdlss.b
    lcdlss.k
    lclkr
    cT
    @9
    cB
    @2
    cD
    @8
    @8
    eqid
    lcdlss.t
    @9
    eqid
    lsslss
    syl2anc
    bitrd
    @7
    @4
    @2
    @0
    wcel
    #
    wa
    @6
    @2
    cT
    @0
    elin
    @11
    @5
    @4
    vu
    cB
    selpw
    anbi2i
    bitr2i
    syl6bb
    eqrdv
end
