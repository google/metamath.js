include "c0p.mm"
include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "cdgr.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "wrex.mm"
include "cc.mm"
include "wss.mm"
include "plybss.mm"
include "ply0.mm"
include "3syl.mm"
include "cc0.mm"
include "cv.mm"
include "cvv.mm"
include "cnex.mm"
include "a1i.mm"
include "wf.mm"
include "wfn.mm"
include "plyf.mm"
include "ffn.mm"
include "inidm.mm"
include "offn.mm"
include "wa.mm"
include "eqidd.mm"
include "0pval.mm"
include "adantl.mm"
include "ofval.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "mul01d.mm"
include "eqtrd.mm"
include "subid1d.mm"
include "offveq.mm"
include "eqeq1d.mm"
include "caddc.mm"
include "fveq2d.mm"
include "cn0.mm"
include "dgrcl.mm"
include "nn0red.mm"
include "recnd.mm"
include "addid2d.mm"
include "eqcomd.mm"
include "breq12d.mm"
include "0red.mm"
include "ltsubaddd.mm"
include "bitr4d.mm"
include "orbi12d.mm"
include "mpbird.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "syl5eq.mm"
include "breq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"

theorem plydivlem3
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
  assume plydiv.r: |- R = ( F oF - ( G oF x. q ) )
  assume plydiv.0: |- ( ph -> ( F = 0p \/ ( ( deg ` F ) - ( deg ` G ) ) < 0 ) )

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
  assert |- ( ph -> E. q e. ( Poly ` S ) ( R = 0p \/ ( deg ` R ) < ( deg ` G ) ) )

  proof
    wph
    c0p
    cS
    cply
    cfv
    #
    wcel
    #
    cF
    cG
    c0p
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
    vq
    @0
    wrex
    wph
    cF
    @0
    wcel
    #
    cS
    cc
    wss
    @1
    plydiv.f
    cS
    cF
    plybss
    cS
    ply0
    3syl
    #
    wph
    @10
    cF
    c0p
    wceq
    #
    cF
    cdgr
    cfv
    #
    @8
    cmin
    co
    cc0
    clt
    wbr
    #
    wo
    plydiv.0
    wph
    @6
    @17
    @9
    @19
    wph
    @5
    cF
    c0p
    wph
    vz
    cc
    vz
    cv
    #
    cF
    cfv
    #
    cc0
    cmin
    cF
    @3
    cF
    cvv
    cc
    cvv
    wcel
    wph
    cnex
    a1i
    #
    wph
    @15
    cc
    cc
    cF
    wf
    #
    cF
    cc
    wfn
    plydiv.f
    cS
    cF
    plyf
    #
    cc
    cc
    cF
    ffn
    3syl
    #
    wph
    cc
    cc
    cmul
    cc
    cG
    c0p
    cvv
    cvv
    wph
    cG
    @0
    wcel
    #
    cc
    cc
    cG
    wf
    #
    cG
    cc
    wfn
    plydiv.g
    cS
    cG
    plyf
    #
    cc
    cc
    cG
    ffn
    3syl
    #
    wph
    @1
    cc
    cc
    c0p
    wf
    c0p
    cc
    wfn
    @16
    cS
    c0p
    plyf
    cc
    cc
    c0p
    ffn
    3syl
    #
    @22
    @22
    cc
    inidm
    #
    offn
    @25
    wph
    @20
    cc
    wcel
    #
    wa
    #
    @21
    eqidd
    @33
    @20
    @3
    cfv
    @20
    cG
    cfv
    #
    cc0
    cmul
    co
    cc0
    wph
    cc
    cc
    @34
    cc0
    cmul
    cc
    cG
    c0p
    cvv
    cvv
    @20
    @29
    @30
    @22
    @22
    @31
    @33
    @34
    eqidd
    @32
    @20
    c0p
    cfv
    cc0
    wceq
    wph
    @20
    0pval
    adantl
    ofval
    @33
    @34
    wph
    cc
    cc
    @20
    cG
    wph
    @26
    @27
    plydiv.g
    @28
    syl
    ffvelrnda
    mul01d
    eqtrd
    @33
    @21
    wph
    cc
    cc
    @20
    cF
    wph
    @15
    @23
    plydiv.f
    @24
    syl
    ffvelrnda
    subid1d
    offveq
    #
    eqeq1d
    wph
    @9
    @18
    cc0
    @8
    caddc
    co
    #
    clt
    wbr
    @19
    wph
    @7
    @18
    @8
    @36
    clt
    wph
    @5
    cF
    cdgr
    @35
    fveq2d
    wph
    @36
    @8
    wph
    @8
    wph
    @8
    wph
    @8
    wph
    @26
    @8
    cn0
    wcel
    plydiv.g
    cS
    cG
    dgrcl
    syl
    nn0red
    #
    recnd
    addid2d
    eqcomd
    breq12d
    wph
    @18
    @8
    cc0
    wph
    @18
    wph
    @15
    @18
    cn0
    wcel
    plydiv.f
    cS
    cF
    dgrcl
    syl
    nn0red
    @37
    wph
    0red
    ltsubaddd
    bitr4d
    orbi12d
    mpbird
    @14
    @10
    vq
    c0p
    @0
    vq
    cv
    #
    c0p
    wceq
    #
    @11
    @6
    @13
    @9
    @39
    cR
    @5
    c0p
    @39
    cR
    cF
    cG
    @38
    @2
    co
    #
    @4
    co
    @5
    plydiv.r
    @39
    @40
    @3
    cF
    @4
    @38
    c0p
    cG
    @2
    oveq2
    oveq2d
    syl5eq
    #
    eqeq1d
    @39
    @12
    @7
    @8
    clt
    @39
    cR
    @5
    cdgr
    @41
    fveq2d
    breq1d
    orbi12d
    rspcev
    syl2anc
end
