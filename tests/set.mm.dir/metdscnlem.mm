include "cfv.mm"
include "cxne.mm"
include "cxad.mm"
include "co.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "wcel.mm"
include "cxr.mm"
include "cxmt.mm"
include "wss.mm"
include "wf.mm"
include "metdsf.mm"
include "syl2anc.mm"
include "ffvelrnd.mm"
include "cle.mm"
include "wbr.mm"
include "elxrge0.mm"
include "simplbi.mm"
include "syl.mm"
include "xnegcld.mm"
include "xaddcld.mm"
include "xmetcl.mm"
include "syl3anc.mm"
include "rpxrd.mm"
include "metdstri.mm"
include "syl22anc.mm"
include "cmnf.mm"
include "wne.mm"
include "wb.mm"
include "simprbi.mm"
include "ge0nemnf.mm"
include "xmetge0.mm"
include "xlesubadd.mm"
include "syl33anc.mm"
include "mpbird.mm"
include "xrlelttrd.mm"

theorem metdscnlem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let vr: setvar r
  let vw: setvar w
  let vz: setvar z
  let vs: setvar s
  let vt: setvar t
  let cG: class G
  let cT: class T
  let cU: class U
  let cV: class V
  assume metdscn.f: |- F = ( x e. X |-> inf ( ran ( y e. S |-> ( x D y ) ) , RR* , < ) )
  assume metdscn.j: |- J = ( MetOpen ` D )
  assume metdscn.c: |- C = ( dist ` RR*s )
  assume metdscn.k: |- K = ( MetOpen ` C )
  assume metdscnlem.1: |- ( ph -> D e. ( *Met ` X ) )
  assume metdscnlem.2: |- ( ph -> S C_ X )
  assume metdscnlem.3: |- ( ph -> A e. X )
  assume metdscnlem.4: |- ( ph -> B e. X )
  assume metdscnlem.5: |- ( ph -> R e. RR+ )
  assume metdscnlem.6: |- ( ph -> ( A D B ) < R )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint D x
  disjoint D y
  disjoint J y
  disjoint B x
  disjoint B y
  disjoint S x
  disjoint S y
  disjoint X x
  disjoint X y
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint r s
  disjoint r t
  disjoint D r
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint D s
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint D t
  disjoint D w
  disjoint D z
  disjoint J r
  disjoint J s
  disjoint J t
  disjoint J w
  disjoint J z
  disjoint ph s
  disjoint ph t
  disjoint C r
  disjoint C s
  disjoint C w
  disjoint C z
  disjoint G s
  disjoint G t
  disjoint R w
  disjoint R z
  disjoint T s
  disjoint T t
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint K r
  disjoint K s
  disjoint K w
  disjoint K z
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint S w
  disjoint S z
  disjoint U s
  disjoint U w
  disjoint X r
  disjoint X s
  disjoint X t
  disjoint X w
  disjoint X z
  disjoint F r
  disjoint F s
  disjoint F t
  disjoint F w
  disjoint F z
  disjoint V w
  disjoint V z
  assert |- ( ph -> ( ( F ` A ) +e -e ( F ` B ) ) < R )

  proof
    wph
    cA
    cF
    cfv
    #
    cB
    cF
    cfv
    #
    cxne
    #
    cxad
    co
    #
    cA
    cB
    cD
    co
    #
    cR
    wph
    @0
    @2
    wph
    @0
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @0
    cxr
    wcel
    #
    wph
    cX
    @5
    cA
    cF
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cS
    cX
    wss
    #
    cX
    @5
    cF
    wf
    metdscnlem.1
    metdscnlem.2
    vx
    vy
    cD
    cS
    cF
    cX
    metdscn.f
    metdsf
    syl2anc
    #
    metdscnlem.3
    ffvelrnd
    #
    @6
    @7
    cc0
    @0
    cle
    wbr
    #
    @0
    elxrge0
    #
    simplbi
    syl
    #
    wph
    @1
    wph
    @1
    @5
    wcel
    #
    @1
    cxr
    wcel
    #
    wph
    cX
    @5
    cB
    cF
    @10
    metdscnlem.4
    ffvelrnd
    #
    @15
    @16
    cc0
    @1
    cle
    wbr
    #
    @1
    elxrge0
    #
    simplbi
    syl
    #
    xnegcld
    xaddcld
    wph
    @8
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    @4
    cxr
    wcel
    #
    metdscnlem.1
    metdscnlem.3
    metdscnlem.4
    cA
    cB
    cD
    cX
    xmetcl
    syl3anc
    #
    wph
    cR
    metdscnlem.5
    rpxrd
    wph
    @3
    @4
    cle
    wbr
    #
    @0
    @4
    @1
    cxad
    co
    cle
    wbr
    #
    wph
    @8
    @9
    @21
    @22
    @26
    metdscnlem.1
    metdscnlem.2
    metdscnlem.3
    metdscnlem.4
    vx
    vy
    cA
    cB
    cD
    cS
    cF
    cX
    metdscn.f
    metdstri
    syl22anc
    wph
    @7
    @16
    @23
    @12
    @1
    cmnf
    wne
    #
    cc0
    @4
    cle
    wbr
    #
    @25
    @26
    wb
    @14
    @20
    @24
    wph
    @6
    @12
    @11
    @6
    @7
    @12
    @13
    simprbi
    syl
    wph
    @16
    @18
    @27
    @20
    wph
    @15
    @18
    @17
    @15
    @16
    @18
    @19
    simprbi
    syl
    @1
    ge0nemnf
    syl2anc
    wph
    @8
    @21
    @22
    @28
    metdscnlem.1
    metdscnlem.3
    metdscnlem.4
    cA
    cB
    cD
    cX
    xmetge0
    syl3anc
    @0
    @1
    @4
    xlesubadd
    syl33anc
    mpbird
    metdscnlem.6
    xrlelttrd
end
