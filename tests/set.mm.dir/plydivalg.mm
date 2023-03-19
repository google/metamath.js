include "c0p.mm"
include "wceq.mm"
include "cdgr.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "cply.mm"
include "wrex.mm"
include "cv.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "cmin.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "plydivex.mm"
include "wcel.mm"
include "caddc.mm"
include "simpll.mm"
include "sylan.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "cdiv.mm"
include "cneg.mm"
include "syl.mm"
include "eqid.mm"
include "simplrr.mm"
include "simprr.mm"
include "simplrl.mm"
include "simprl.mm"
include "plydiveu.mm"
include "ex.mm"
include "ralrimivva.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "syl5eq.mm"
include "eqeq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "orbi12d.mm"
include "reu4.mm"
include "sylanbrc.mm"

theorem plydivalg
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let vq: setvar q
  let vp: setvar p
  let vz: setvar z
  let cA: class A
  let vd: setvar d
  let vf: setvar f
  let cH: class H
  let cB: class B
  let cD: class D
  let cM: class M
  let cN: class N
  let cT: class T
  let vg: setvar g
  let vw: setvar w
  assume plydiv.pl: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x + y ) e. S )
  assume plydiv.tm: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x x. y ) e. S )
  assume plydiv.rc: |- ( ( ph /\ ( x e. S /\ x =/= 0 ) ) -> ( 1 / x ) e. S )
  assume plydiv.m1: |- ( ph -> -u 1 e. S )
  assume plydiv.f: |- ( ph -> F e. ( Poly ` S ) )
  assume plydiv.g: |- ( ph -> G e. ( Poly ` S ) )
  assume plydiv.z: |- ( ph -> G =/= 0p )
  assume plydiv.r: |- R = ( F oF - ( G oF x. q ) )

  disjoint ph q
  disjoint x y
  disjoint q x
  disjoint q y
  disjoint F q
  disjoint F x
  disjoint F y
  disjoint ph x
  disjoint ph y
  disjoint G q
  disjoint G x
  disjoint G y
  disjoint R x
  disjoint R y
  disjoint S q
  disjoint S x
  disjoint S y
  disjoint p q
  disjoint p ph
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint d f
  disjoint d p
  disjoint d q
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint F d
  disjoint f p
  disjoint f q
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint p q
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint F p
  disjoint q z
  disjoint F z
  disjoint H f
  disjoint H p
  disjoint H q
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint d ph
  disjoint ph z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint D f
  disjoint D z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint N f
  disjoint N p
  disjoint N q
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint T x
  disjoint T y
  disjoint d g
  disjoint d w
  disjoint G d
  disjoint f g
  disjoint f w
  disjoint G f
  disjoint g p
  disjoint g q
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint G g
  disjoint p w
  disjoint G p
  disjoint q w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint G z
  disjoint R d
  disjoint R f
  disjoint R p
  disjoint S d
  disjoint S f
  disjoint S g
  disjoint S p
  disjoint S z
  assert |- ( ph -> E! q e. ( Poly ` S ) ( R = 0p \/ ( deg ` R ) < ( deg ` G ) ) )

  proof
    wph
    cR
    c0p
    wceq
    #
    cR
    cdgr
    cfv
    #
    cG
    cdgr
    cfv
    #
    clt
    wbr
    #
    wo
    #
    vq
    cS
    cply
    cfv
    #
    wrex
    @4
    cF
    cG
    vp
    cv
    #
    cmul
    cof
    #
    co
    #
    cmin
    cof
    #
    co
    #
    c0p
    wceq
    #
    @10
    cdgr
    cfv
    #
    @2
    clt
    wbr
    #
    wo
    #
    wa
    #
    vq
    cv
    #
    @6
    wceq
    #
    wi
    #
    vp
    @5
    wral
    vq
    @5
    wral
    @4
    vq
    @5
    wreu
    wph
    vx
    vy
    cR
    cS
    cF
    cG
    vq
    plydiv.pl
    plydiv.tm
    plydiv.rc
    plydiv.m1
    plydiv.f
    plydiv.g
    plydiv.z
    plydiv.r
    plydivex
    wph
    @18
    vq
    vp
    @5
    @5
    wph
    @16
    @5
    wcel
    #
    @6
    @5
    wcel
    #
    wa
    #
    wa
    #
    @15
    @17
    @22
    @15
    wa
    #
    vx
    vy
    @10
    cS
    cR
    cF
    cG
    vp
    vq
    @23
    wph
    vx
    cv
    #
    cS
    wcel
    #
    vy
    cv
    #
    cS
    wcel
    wa
    #
    @24
    @26
    caddc
    co
    cS
    wcel
    wph
    @21
    @15
    simpll
    #
    plydiv.pl
    sylan
    @23
    wph
    @27
    @24
    @26
    cmul
    co
    cS
    wcel
    @28
    plydiv.tm
    sylan
    @23
    wph
    @25
    @24
    cc0
    wne
    wa
    c1
    @24
    cdiv
    co
    cS
    wcel
    @28
    plydiv.rc
    sylan
    @23
    wph
    c1
    cneg
    cS
    wcel
    @28
    plydiv.m1
    syl
    @23
    wph
    cF
    @5
    wcel
    @28
    plydiv.f
    syl
    @23
    wph
    cG
    @5
    wcel
    @28
    plydiv.g
    syl
    @23
    wph
    cG
    c0p
    wne
    @28
    plydiv.z
    syl
    @10
    eqid
    wph
    @19
    @20
    @15
    simplrr
    @22
    @4
    @14
    simprr
    plydiv.r
    wph
    @19
    @20
    @15
    simplrl
    @22
    @4
    @14
    simprl
    plydiveu
    ex
    ralrimivva
    @4
    @14
    vq
    vp
    @5
    @17
    @0
    @11
    @3
    @13
    @17
    cR
    @10
    c0p
    @17
    cR
    cF
    cG
    @16
    @7
    co
    #
    @9
    co
    @10
    plydiv.r
    @17
    @29
    @8
    cF
    @9
    @16
    @6
    cG
    @7
    oveq2
    oveq2d
    syl5eq
    #
    eqeq1d
    @17
    @1
    @12
    @2
    clt
    @17
    cR
    @10
    cdgr
    @30
    fveq2d
    breq1d
    orbi12d
    reu4
    sylanbrc
end
