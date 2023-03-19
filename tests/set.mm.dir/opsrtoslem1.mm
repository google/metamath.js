include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "cfv.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "weq.mm"
include "wo.mm"
include "copab.mm"
include "cxp.mm"
include "cin.mm"
include "cid.mm"
include "cres.mm"
include "cun.mm"
include "opsrle.mm"
include "unopab.mm"
include "wcel.mm"
include "inopab.mm"
include "df-xp.mm"
include "ineq2i.mm"
include "vex.mm"
include "prss.mm"
include "anbi1i.mm"
include "ancom.mm"
include "bitr3i.mm"
include "opabbii.mm"
include "3eqtr4i.mm"
include "opabresid.mm"
include "equcom.mm"
include "anbi2i.mm"
include "eleq1.mm"
include "biimpac.mm"
include "pm4.71i.mm"
include "an32.mm"
include "3bitri.mm"
include "eqtr3i.mm"
include "uneq12i.mm"
include "orbi1i.mm"
include "andi.mm"
include "3eqtr4ri.mm"
include "syl6eq.mm"

theorem opsrtoslem1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let c.lt: class .<
  let cT: class T
  let vh: setvar h
  let cI: class I
  let c.le: class .<_
  let cO: class O
  let cV: class V
  let va: setvar a
  let vb: setvar b
  assume opsrso.o: |- O = ( ( I ordPwSer R ) ` T )
  assume opsrso.i: |- ( ph -> I e. V )
  assume opsrso.r: |- ( ph -> R e. Toset )
  assume opsrso.t: |- ( ph -> T C_ ( I X. I ) )
  assume opsrso.w: |- ( ph -> T We I )
  assume opsrtoslem.s: |- S = ( I mPwSer R )
  assume opsrtoslem.b: |- B = ( Base ` S )
  assume opsrtoslem.q: |- .< = ( lt ` R )
  assume opsrtoslem.c: |- C = ( T <bag I )
  assume opsrtoslem.d: |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin }
  assume opsrtoslem.ps: |- ( ps <-> E. z e. D ( ( x ` z ) .< ( y ` z ) /\ A. w e. D ( w C z -> ( x ` w ) = ( y ` w ) ) ) )
  assume opsrtoslem.l: |- .<_ = ( le ` O )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint I h
  disjoint I w
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint h ph
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint .< w
  disjoint .< x
  disjoint .< y
  disjoint .< z
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint B a
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint a h
  disjoint a w
  disjoint a z
  disjoint a ph
  disjoint b h
  disjoint b w
  disjoint b z
  disjoint b ph
  disjoint a ps
  disjoint b ps
  assert |- ( ph -> .<_ = ( ( { <. x , y >. | ps } i^i ( B X. B ) ) u. ( _I |` B ) ) )

  proof
    wph
    c.le
    vx
    cv
    #
    vy
    cv
    #
    cpr
    cB
    wss
    #
    vz
    cv
    #
    @0
    cfv
    @3
    @1
    cfv
    c.lt
    wbr
    vw
    cv
    #
    @3
    cC
    wbr
    @4
    @0
    cfv
    @4
    @1
    cfv
    wceq
    wi
    vw
    cD
    wral
    wa
    vz
    cD
    wrex
    #
    vx
    vy
    weq
    #
    wo
    #
    wa
    #
    vx
    vy
    copab
    #
    wps
    vx
    vy
    copab
    #
    cB
    cB
    cxp
    #
    cin
    #
    cid
    cB
    cres
    #
    cun
    #
    wph
    vx
    vy
    vz
    vw
    cB
    cC
    cD
    cR
    cS
    c.lt
    cT
    vh
    cI
    c.le
    cO
    opsrtoslem.s
    opsrso.o
    opsrtoslem.b
    opsrtoslem.q
    opsrtoslem.c
    opsrtoslem.d
    opsrtoslem.l
    opsrso.t
    opsrle
    @2
    wps
    wa
    #
    vx
    vy
    copab
    #
    @2
    @6
    wa
    #
    vx
    vy
    copab
    #
    cun
    @15
    @17
    wo
    #
    vx
    vy
    copab
    @14
    @9
    @15
    @17
    vx
    vy
    unopab
    @12
    @16
    @13
    @18
    @10
    @0
    cB
    wcel
    #
    @1
    cB
    wcel
    #
    wa
    #
    vx
    vy
    copab
    #
    cin
    wps
    @22
    wa
    #
    vx
    vy
    copab
    @12
    @16
    wps
    @22
    vx
    vy
    inopab
    @11
    @23
    @10
    vx
    vy
    cB
    cB
    df-xp
    ineq2i
    @15
    @24
    vx
    vy
    @15
    @22
    wps
    wa
    @24
    @22
    @2
    wps
    @0
    @1
    cB
    vx
    vex
    vy
    vex
    prss
    #
    anbi1i
    @22
    wps
    ancom
    bitr3i
    opabbii
    3eqtr4i
    @20
    vy
    vx
    weq
    #
    wa
    #
    vx
    vy
    copab
    @13
    @18
    vx
    vy
    cB
    opabresid
    @27
    @17
    vx
    vy
    @27
    @20
    @6
    wa
    #
    @21
    wa
    #
    @22
    @6
    wa
    @17
    @27
    @28
    @29
    @6
    @26
    @20
    vx
    vy
    equcom
    anbi2i
    @28
    @21
    @6
    @20
    @21
    @0
    @1
    cB
    eleq1
    biimpac
    pm4.71i
    bitr3i
    @20
    @6
    @21
    an32
    @22
    @2
    @6
    @25
    anbi1i
    3bitri
    opabbii
    eqtr3i
    uneq12i
    @8
    @19
    vx
    vy
    @8
    @2
    wps
    @6
    wo
    #
    wa
    @19
    @30
    @7
    @2
    wps
    @5
    @6
    opsrtoslem.ps
    orbi1i
    anbi2i
    @2
    wps
    @6
    andi
    bitr3i
    opabbii
    3eqtr4ri
    syl6eq
end
