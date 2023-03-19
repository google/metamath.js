include "cquot.mm"
include "co.mm"
include "cv.mm"
include "cmul.mm"
include "cof.mm"
include "cmin.mm"
include "c0p.mm"
include "wceq.mm"
include "cdgr.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "cply.mm"
include "crab.mm"
include "wcel.mm"
include "wa.mm"
include "crio.mm"
include "cc.mm"
include "wne.mm"
include "eqid.mm"
include "quotval.mm"
include "syl3anc.mm"
include "wrex.mm"
include "wreu.mm"
include "plydivalg.mm"
include "reurex.mm"
include "syl.mm"
include "caddc.mm"
include "addcl.mm"
include "adantl.mm"
include "mulcl.mm"
include "cc0.mm"
include "c1.mm"
include "cdiv.mm"
include "reccl.mm"
include "cneg.mm"
include "neg1cn.mm"
include "a1i.mm"
include "plyssc.mm"
include "sseldi.mm"
include "wss.mm"
include "wi.mm"
include "wral.mm"
include "id.mm"
include "rgenw.mm"
include "riotass2.mm"
include "mpanl12.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "riotacl2.mm"
include "eqeltrd.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "syl6eqr.mm"
include "eqeq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "orbi12d.mm"
include "elrab.mm"
include "sylib.mm"

theorem quotlem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let vq: setvar q
  let vz: setvar z
  let cA: class A
  let vd: setvar d
  let vf: setvar f
  let vp: setvar p
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
  assume quotlem.8: |- R = ( F oF - ( G oF x. ( F quot G ) ) )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint ph x
  disjoint ph y
  disjoint G x
  disjoint G y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint R q
  disjoint ph q
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
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint F q
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
  disjoint G q
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
  disjoint S q
  disjoint S z
  assert |- ( ph -> ( ( F quot G ) e. ( Poly ` S ) /\ ( R = 0p \/ ( deg ` R ) < ( deg ` G ) ) ) )

  proof
    wph
    cF
    cG
    cquot
    co
    #
    cF
    cG
    vq
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
    @5
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
    crab
    #
    wcel
    @0
    @11
    wcel
    cR
    c0p
    wceq
    #
    cR
    cdgr
    cfv
    #
    @8
    clt
    wbr
    #
    wo
    #
    wa
    wph
    @0
    @10
    vq
    @11
    crio
    #
    @12
    wph
    @0
    @10
    vq
    cc
    cply
    cfv
    #
    crio
    #
    @17
    wph
    cF
    @11
    wcel
    cG
    @11
    wcel
    cG
    c0p
    wne
    @0
    @19
    wceq
    plydiv.f
    plydiv.g
    plydiv.z
    @5
    cS
    cF
    cG
    vq
    @5
    eqid
    #
    quotval
    syl3anc
    wph
    @10
    vq
    @11
    wrex
    #
    @10
    vq
    @18
    wreu
    #
    @17
    @19
    wceq
    #
    wph
    @10
    vq
    @11
    wreu
    #
    @21
    wph
    vx
    vy
    @5
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
    @20
    plydivalg
    #
    @10
    vq
    @11
    reurex
    syl
    wph
    vx
    vy
    @5
    cc
    cF
    cG
    vq
    vx
    cv
    #
    cc
    wcel
    #
    vy
    cv
    #
    cc
    wcel
    wa
    #
    @26
    @28
    caddc
    co
    cc
    wcel
    wph
    @26
    @28
    addcl
    adantl
    @29
    @26
    @28
    cmul
    co
    cc
    wcel
    wph
    @26
    @28
    mulcl
    adantl
    @27
    @26
    cc0
    wne
    wa
    c1
    @26
    cdiv
    co
    cc
    wcel
    wph
    @26
    reccl
    adantl
    c1
    cneg
    cc
    wcel
    wph
    neg1cn
    a1i
    wph
    @11
    @18
    cF
    cS
    plyssc
    #
    plydiv.f
    sseldi
    wph
    @11
    @18
    cG
    @30
    plydiv.g
    sseldi
    plydiv.z
    @20
    plydivalg
    @11
    @18
    wss
    @10
    @10
    wi
    #
    vq
    @11
    wral
    @21
    @22
    wa
    @23
    @30
    @31
    vq
    @11
    @10
    id
    rgenw
    @10
    @10
    vq
    @11
    @18
    riotass2
    mpanl12
    syl2anc
    eqtr4d
    wph
    @24
    @17
    @12
    wcel
    @25
    @10
    vq
    @11
    riotacl2
    syl
    eqeltrd
    @10
    @16
    vq
    @0
    @11
    @1
    @0
    wceq
    #
    @6
    @13
    @9
    @15
    @32
    @5
    cR
    c0p
    @32
    @5
    cF
    cG
    @0
    @2
    co
    #
    @4
    co
    cR
    @32
    @3
    @33
    cF
    @4
    @1
    @0
    cG
    @2
    oveq2
    oveq2d
    quotlem.8
    syl6eqr
    #
    eqeq1d
    @32
    @7
    @14
    @8
    clt
    @32
    @5
    cR
    cdgr
    @34
    fveq2d
    breq1d
    orbi12d
    elrab
    sylib
end
