include "cv.mm"
include "cpr.mm"
include "chash.mm"
include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "wss.mm"
include "cplusg.mm"
include "cmpt.mm"
include "crn.mm"
include "cmpt2.mm"
include "wrex.mm"
include "wa.mm"
include "copab.mm"
include "cec.mm"
include "cpc.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "csubg.mm"
include "eqid.mm"
include "oveq2.mm"
include "cbvmptv.mm"
include "oveq1.mm"
include "mpteq2dv.mm"
include "syl5eq.mm"
include "rneqd.mm"
include "mpteq1.mm"
include "cbvmpt2v.mm"
include "preq12.mm"
include "sseq1d.mm"
include "id.mm"
include "eqeqan12d.mm"
include "rexbidv.mm"
include "anbi12d.mm"
include "cbvopabv.mm"
include "sylow1lem3.mm"
include "wcel.mm"
include "cgrp.mm"
include "adantr.mm"
include "cfn.mm"
include "cprime.mm"
include "cn0.mm"
include "cdvds.mm"
include "simprl.mm"
include "simprr.mm"
include "sylow1lem5.mm"
include "rexlimddv.mm"

theorem sylow1
  let wph: wff ph
  let cP: class P
  let vg: setvar g
  let cG: class G
  let cN: class N
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vs: setvar s
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vh: setvar h
  let cH: class H
  let vw: setvar w
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let vt: setvar t
  let vv: setvar v
  let c.pl: class .+
  let c.sm: class .~
  let c.po: class .(+)
  assume sylow1.x: |- X = ( Base ` G )
  assume sylow1.g: |- ( ph -> G e. Grp )
  assume sylow1.f: |- ( ph -> X e. Fin )
  assume sylow1.p: |- ( ph -> P e. Prime )
  assume sylow1.n: |- ( ph -> N e. NN0 )
  assume sylow1.d: |- ( ph -> ( P ^ N ) || ( # ` X ) )

  disjoint N g
  disjoint X g
  disjoint G g
  disjoint P g
  disjoint g ph
  disjoint a b
  disjoint a c
  disjoint a g
  disjoint a s
  disjoint a u
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint B a
  disjoint b c
  disjoint b g
  disjoint b s
  disjoint b u
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint B b
  disjoint c g
  disjoint c s
  disjoint c u
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint g s
  disjoint g u
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint s u
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint B s
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint a h
  disjoint H a
  disjoint b h
  disjoint H b
  disjoint c h
  disjoint H c
  disjoint g h
  disjoint H g
  disjoint h x
  disjoint h y
  disjoint H h
  disjoint H x
  disjoint H y
  disjoint a w
  disjoint S a
  disjoint b w
  disjoint S b
  disjoint c w
  disjoint S c
  disjoint g w
  disjoint S g
  disjoint u w
  disjoint S u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint a k
  disjoint a n
  disjoint a t
  disjoint a v
  disjoint N a
  disjoint b k
  disjoint b n
  disjoint b t
  disjoint b v
  disjoint N b
  disjoint g k
  disjoint g n
  disjoint g t
  disjoint g v
  disjoint h k
  disjoint h n
  disjoint h s
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h z
  disjoint N h
  disjoint k n
  disjoint k s
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint N k
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint N n
  disjoint s t
  disjoint s v
  disjoint s w
  disjoint N s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint N t
  disjoint u v
  disjoint N u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint N v
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint X a
  disjoint X b
  disjoint c k
  disjoint c n
  disjoint c t
  disjoint c v
  disjoint X c
  disjoint X h
  disjoint X k
  disjoint X n
  disjoint X s
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint .+ b
  disjoint .+ c
  disjoint .+ s
  disjoint .+ u
  disjoint .+ v
  disjoint .+ w
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint .~ a
  disjoint .~ w
  disjoint .~ z
  disjoint .(+) a
  disjoint .(+) b
  disjoint .(+) c
  disjoint .(+) g
  disjoint .(+) u
  disjoint .(+) w
  disjoint .(+) x
  disjoint .(+) y
  disjoint .(+) z
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G h
  disjoint G k
  disjoint G s
  disjoint G t
  disjoint G u
  disjoint G v
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint P a
  disjoint P b
  disjoint P h
  disjoint P k
  disjoint P n
  disjoint P s
  disjoint P t
  disjoint P u
  disjoint P v
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint n ph
  disjoint ph t
  disjoint ph u
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint h ph
  assert |- ( ph -> E. g e. ( SubGrp ` G ) ( # ` g ) = ( P ^ N ) )

  proof
    wph
    cP
    vh
    cv
    #
    va
    cv
    #
    vb
    cv
    #
    cpr
    #
    vs
    cv
    #
    chash
    cfv
    cP
    cN
    cexp
    co
    #
    wceq
    vs
    cX
    cpw
    crab
    #
    wss
    #
    vk
    cv
    #
    @1
    vu
    vv
    cX
    @6
    vs
    vv
    cv
    #
    vu
    cv
    #
    @4
    cG
    cplusg
    cfv
    #
    co
    #
    cmpt
    #
    crn
    #
    cmpt2
    #
    co
    #
    @2
    wceq
    #
    vk
    cX
    wrex
    #
    wa
    #
    va
    vb
    copab
    #
    cec
    chash
    cfv
    cpc
    co
    cP
    cX
    chash
    cfv
    #
    cpc
    co
    cN
    cmin
    co
    cle
    wbr
    #
    vg
    cv
    chash
    cfv
    @5
    wceq
    vg
    cG
    csubg
    cfv
    wrex
    vh
    @6
    wph
    vx
    vy
    vz
    vh
    cP
    @11
    @15
    @20
    @6
    vk
    cG
    cN
    cX
    vs
    sylow1.x
    sylow1.g
    sylow1.f
    sylow1.p
    sylow1.n
    sylow1.d
    @11
    eqid
    #
    @6
    eqid
    #
    vu
    vv
    vx
    vy
    cX
    @6
    @14
    vz
    vy
    cv
    #
    vx
    cv
    #
    vz
    cv
    #
    @11
    co
    #
    cmpt
    #
    crn
    vz
    @9
    @28
    cmpt
    #
    crn
    @10
    @26
    wceq
    #
    @13
    @30
    @31
    @13
    vz
    @9
    @10
    @27
    @11
    co
    #
    cmpt
    @30
    vs
    vz
    @9
    @12
    @32
    @4
    @27
    @10
    @11
    oveq2
    cbvmptv
    @31
    vz
    @9
    @32
    @28
    @10
    @26
    @27
    @11
    oveq1
    mpteq2dv
    syl5eq
    rneqd
    @9
    @25
    wceq
    @30
    @29
    vz
    @9
    @25
    @28
    mpteq1
    rneqd
    cbvmpt2v
    #
    @19
    @26
    @25
    cpr
    #
    @6
    wss
    #
    @8
    @26
    @15
    co
    #
    @25
    wceq
    #
    vk
    cX
    wrex
    #
    wa
    va
    vb
    vx
    vy
    @1
    @26
    wceq
    #
    @2
    @25
    wceq
    #
    wa
    #
    @7
    @35
    @18
    @38
    @41
    @3
    @34
    @6
    @1
    @2
    @26
    @25
    preq12
    sseq1d
    @41
    @17
    @37
    vk
    cX
    @39
    @40
    @16
    @36
    @2
    @25
    @1
    @26
    @8
    @15
    oveq2
    @40
    id
    eqeqan12d
    rexbidv
    anbi12d
    cbvopabv
    #
    sylow1lem3
    wph
    @0
    @6
    wcel
    #
    @22
    wa
    #
    wa
    vx
    vy
    vz
    vt
    @0
    cP
    @11
    @15
    @20
    @6
    vk
    vg
    cG
    vt
    cv
    @0
    @15
    co
    @0
    wceq
    vt
    cX
    crab
    #
    cN
    cX
    vs
    sylow1.x
    wph
    cG
    cgrp
    wcel
    @44
    sylow1.g
    adantr
    wph
    cX
    cfn
    wcel
    @44
    sylow1.f
    adantr
    wph
    cP
    cprime
    wcel
    @44
    sylow1.p
    adantr
    wph
    cN
    cn0
    wcel
    @44
    sylow1.n
    adantr
    wph
    @5
    @21
    cdvds
    wbr
    @44
    sylow1.d
    adantr
    @23
    @24
    @33
    @42
    wph
    @43
    @22
    simprl
    @45
    eqid
    wph
    @43
    @22
    simprr
    sylow1lem5
    rexlimddv
end
