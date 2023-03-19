include "wcel.mm"
include "c0.mm"
include "cvv.mm"
include "cop.mm"
include "wceq.mm"
include "0ex.mm"
include "a1i.mm"
include "cc0.mm"
include "cs2.mm"
include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "wrmo.mm"
include "wreu.mm"
include "crn.mm"
include "ciun.mm"
include "cdif.mm"
include "difss.mm"
include "eqsstri.mm"
include "co.mm"
include "cin.mm"
include "inss1.mm"
include "frgpnabllem1.mm"
include "sseldi.mm"
include "c1.mm"
include "cmin.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "wa.mm"
include "cword.mm"
include "csn.mm"
include "crab.mm"
include "cmpt.mm"
include "eqid.mm"
include "efgredeu.mm"
include "reurmo.mm"
include "3syl.mm"
include "cec.mm"
include "wer.mm"
include "cqs.mm"
include "efger.mm"
include "cbs.mm"
include "cgrp.mm"
include "frgpgrp.mm"
include "syl.mm"
include "wf.mm"
include "vrgpf.mm"
include "ffvelrnd.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "c2o.mm"
include "cxp.mm"
include "cfrmd.mm"
include "cqus.mm"
include "frgpval.mm"
include "cid.mm"
include "con0.mm"
include "2on.mm"
include "xpexg.mm"
include "sylancl.mm"
include "wrdexg.mm"
include "fvi.mm"
include "syl5eq.mm"
include "frmdbas.mm"
include "eqtr4d.mm"
include "cefg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fvexd.mm"
include "qusbas.mm"
include "eleqtrrd.mm"
include "inss2.mm"
include "qsel.mm"
include "eqtr3d.mm"
include "erth.mm"
include "mpbird.mm"
include "erref.mm"
include "breq1.mm"
include "rmoi.mm"
include "syl122anc.mm"
include "fveq1d.mm"
include "opex.mm"
include "s2fv0.mm"
include "ax-mp.mm"
include "3eqtr3g.mm"
include "opthg.mm"
include "simprbda.mm"
include "syl21anc.mm"

theorem frgpnabllem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let c.sm: class .~
  let cT: class T
  let cU: class U
  let vn: setvar n
  let cG: class G
  let cI: class I
  let cM: class M
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let vm: setvar m
  let vt: setvar t
  let vk: setvar k
  assume frgpnabl.g: |- G = ( freeGrp ` I )
  assume frgpnabl.w: |- W = ( _I ` Word ( I X. 2o ) )
  assume frgpnabl.r: |- .~ = ( ~FG ` I )
  assume frgpnabl.p: |- .+ = ( +g ` G )
  assume frgpnabl.m: |- M = ( y e. I , z e. 2o |-> <. y , ( 1o \ z ) >. )
  assume frgpnabl.t: |- T = ( v e. W |-> ( n e. ( 0 ... ( # ` v ) ) , w e. ( I X. 2o ) |-> ( v splice <. n , n , <" w ( M ` w ) "> >. ) ) )
  assume frgpnabl.d: |- D = ( W \ U_ x e. W ran ( T ` x ) )
  assume frgpnabl.u: |- U = ( varFGrp ` I )
  assume frgpnabl.i: |- ( ph -> I e. _V )
  assume frgpnabl.a: |- ( ph -> A e. I )
  assume frgpnabl.b: |- ( ph -> B e. I )
  assume frgpnabl.n: |- ( ph -> ( ( U ` A ) .+ ( U ` B ) ) = ( ( U ` B ) .+ ( U ` A ) ) )

  disjoint A x
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint I n
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint I v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint I w
  disjoint x y
  disjoint x z
  disjoint I x
  disjoint y z
  disjoint I y
  disjoint I z
  disjoint ph x
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint B x
  disjoint W n
  disjoint W v
  disjoint W w
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint G x
  disjoint M n
  disjoint M v
  disjoint M w
  disjoint M x
  disjoint T x
  disjoint a b
  disjoint a d
  disjoint a x
  disjoint A a
  disjoint b d
  disjoint b x
  disjoint A b
  disjoint d x
  disjoint A d
  disjoint d m
  disjoint d t
  disjoint D d
  disjoint m t
  disjoint D m
  disjoint D t
  disjoint a m
  disjoint a n
  disjoint a t
  disjoint a v
  disjoint a w
  disjoint a y
  disjoint a z
  disjoint I a
  disjoint b m
  disjoint b n
  disjoint b t
  disjoint b v
  disjoint b w
  disjoint b y
  disjoint b z
  disjoint I b
  disjoint m n
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint I m
  disjoint n t
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint I t
  disjoint a ph
  disjoint b ph
  disjoint .~ a
  disjoint .~ b
  disjoint d y
  disjoint d z
  disjoint .~ d
  disjoint .~ m
  disjoint .~ t
  disjoint B a
  disjoint B b
  disjoint B d
  disjoint a k
  disjoint W a
  disjoint b k
  disjoint W b
  disjoint d k
  disjoint d n
  disjoint d v
  disjoint d w
  disjoint W d
  disjoint k m
  disjoint k n
  disjoint k t
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint W k
  disjoint W m
  disjoint W t
  disjoint G a
  disjoint G b
  disjoint M a
  disjoint M b
  disjoint M m
  disjoint M t
  disjoint T a
  disjoint T b
  disjoint T d
  disjoint T k
  disjoint T m
  disjoint T t
  assert |- ( ph -> A = B )

  proof
    wph
    cA
    cI
    wcel
    #
    c0
    cvv
    wcel
    #
    cA
    c0
    cop
    #
    cB
    c0
    cop
    #
    wceq
    #
    cA
    cB
    wceq
    #
    frgpnabl.a
    @1
    wph
    0ex
    a1i
    wph
    cc0
    @2
    @3
    cs2
    #
    cfv
    #
    cc0
    @3
    @2
    cs2
    #
    cfv
    #
    @2
    @3
    wph
    cc0
    @6
    @8
    wph
    vd
    cv
    #
    @8
    c.sm
    wbr
    #
    vd
    cD
    wrmo
    #
    @6
    cD
    wcel
    @6
    @8
    c.sm
    wbr
    #
    @8
    cD
    wcel
    @8
    @8
    c.sm
    wbr
    #
    @6
    @8
    wceq
    wph
    @8
    cW
    wcel
    @11
    vd
    cD
    wreu
    @12
    wph
    cD
    cW
    @8
    cD
    cW
    vx
    cW
    vx
    cv
    cT
    cfv
    crn
    ciun
    #
    cdif
    cW
    frgpnabl.d
    cW
    @15
    difss
    eqsstri
    #
    wph
    cD
    cB
    cU
    cfv
    #
    cA
    cU
    cfv
    #
    c.pl
    co
    #
    cin
    #
    cD
    @8
    cD
    @19
    inss1
    wph
    vx
    vy
    vz
    vw
    vv
    cB
    cA
    cD
    c.pl
    c.sm
    cT
    cU
    vn
    cG
    cI
    cM
    cW
    frgpnabl.g
    frgpnabl.w
    frgpnabl.r
    frgpnabl.p
    frgpnabl.m
    frgpnabl.t
    frgpnabl.d
    frgpnabl.u
    frgpnabl.i
    frgpnabl.b
    frgpnabl.a
    frgpnabllem1
    #
    sseldi
    #
    sseldi
    #
    vx
    vy
    vz
    vw
    vv
    vt
    @8
    cD
    c.sm
    vm
    cc0
    vt
    cv
    #
    cfv
    cD
    wcel
    vk
    cv
    #
    @24
    cfv
    @25
    c1
    cmin
    co
    @24
    cfv
    cT
    cfv
    crn
    wcel
    vk
    c1
    @24
    chash
    cfv
    cfzo
    co
    wral
    wa
    vt
    cW
    cword
    c0
    csn
    cdif
    crab
    vm
    cv
    #
    chash
    cfv
    c1
    cmin
    co
    @26
    cfv
    cmpt
    #
    cT
    vk
    vm
    vn
    cI
    cM
    cW
    vd
    frgpnabl.w
    frgpnabl.r
    frgpnabl.m
    frgpnabl.t
    frgpnabl.d
    @27
    eqid
    efgredeu
    @11
    vd
    cD
    reurmo
    3syl
    wph
    cD
    @18
    @17
    c.pl
    co
    #
    cin
    #
    cD
    @6
    cD
    @28
    inss1
    wph
    vx
    vy
    vz
    vw
    vv
    cA
    cB
    cD
    c.pl
    c.sm
    cT
    cU
    vn
    cG
    cI
    cM
    cW
    frgpnabl.g
    frgpnabl.w
    frgpnabl.r
    frgpnabl.p
    frgpnabl.m
    frgpnabl.t
    frgpnabl.d
    frgpnabl.u
    frgpnabl.i
    frgpnabl.a
    frgpnabl.b
    frgpnabllem1
    #
    sseldi
    #
    wph
    @13
    @6
    c.sm
    cec
    #
    @8
    c.sm
    cec
    #
    wceq
    wph
    @28
    @32
    @33
    wph
    cW
    c.sm
    wer
    #
    @28
    cW
    c.sm
    cqs
    #
    wcel
    #
    @6
    @28
    wcel
    @28
    @32
    wceq
    @34
    wph
    c.sm
    cI
    cW
    frgpnabl.w
    frgpnabl.r
    efger
    a1i
    #
    wph
    @28
    cG
    cbs
    cfv
    #
    @35
    wph
    cG
    cgrp
    wcel
    #
    @18
    @38
    wcel
    @17
    @38
    wcel
    @28
    @38
    wcel
    wph
    cI
    cvv
    wcel
    #
    @39
    frgpnabl.i
    cG
    cI
    cvv
    frgpnabl.g
    frgpgrp
    syl
    wph
    cI
    @38
    cA
    cU
    wph
    @40
    cI
    @38
    cU
    wf
    frgpnabl.i
    c.sm
    cU
    cG
    cI
    cvv
    @38
    frgpnabl.r
    frgpnabl.u
    frgpnabl.g
    @38
    eqid
    #
    vrgpf
    syl
    #
    frgpnabl.a
    ffvelrnd
    wph
    cI
    @38
    cB
    cU
    @42
    frgpnabl.b
    ffvelrnd
    @38
    c.pl
    cG
    @18
    @17
    @41
    frgpnabl.p
    grpcl
    syl3anc
    wph
    c.sm
    cI
    c2o
    cxp
    #
    cfrmd
    cfv
    #
    cG
    cW
    cvv
    cvv
    wph
    @40
    cG
    @44
    c.sm
    cqus
    co
    wceq
    frgpnabl.i
    c.sm
    cG
    cI
    @44
    cvv
    frgpnabl.g
    @44
    eqid
    #
    frgpnabl.r
    frgpval
    syl
    wph
    cW
    @43
    cword
    #
    @44
    cbs
    cfv
    #
    wph
    cW
    @46
    cid
    cfv
    #
    @46
    frgpnabl.w
    wph
    @43
    cvv
    wcel
    #
    @46
    cvv
    wcel
    @48
    @46
    wceq
    wph
    @40
    c2o
    con0
    wcel
    @49
    frgpnabl.i
    2on
    cI
    c2o
    cvv
    con0
    xpexg
    sylancl
    #
    @43
    cvv
    wrdexg
    @46
    cvv
    fvi
    3syl
    syl5eq
    wph
    @49
    @47
    @46
    wceq
    @50
    @47
    @43
    @44
    cvv
    @45
    @47
    eqid
    frmdbas
    syl
    eqtr4d
    c.sm
    cvv
    wcel
    wph
    c.sm
    cI
    cefg
    cfv
    cvv
    frgpnabl.r
    cI
    cefg
    fvex
    eqeltri
    a1i
    wph
    @43
    cfrmd
    fvexd
    qusbas
    eleqtrrd
    #
    wph
    @29
    @28
    @6
    cD
    @28
    inss2
    @30
    sseldi
    cW
    @28
    @6
    c.sm
    cW
    qsel
    syl3anc
    wph
    @34
    @36
    @8
    @28
    wcel
    @28
    @33
    wceq
    @37
    @51
    wph
    @8
    @19
    @28
    wph
    @20
    @19
    @8
    cD
    @19
    inss2
    @21
    sseldi
    frgpnabl.n
    eleqtrrd
    cW
    @28
    @8
    c.sm
    cW
    qsel
    syl3anc
    eqtr3d
    wph
    @6
    @8
    c.sm
    cW
    @37
    wph
    cD
    cW
    @6
    @16
    @31
    sseldi
    erth
    mpbird
    @22
    wph
    @8
    c.sm
    cW
    @37
    @23
    erref
    @11
    @13
    @14
    vd
    cD
    @6
    @8
    @10
    @6
    @8
    c.sm
    breq1
    @10
    @8
    @8
    c.sm
    breq1
    rmoi
    syl122anc
    fveq1d
    @2
    cvv
    wcel
    @7
    @2
    wceq
    cA
    c0
    opex
    @2
    @3
    cvv
    s2fv0
    ax-mp
    @3
    cvv
    wcel
    @9
    @3
    wceq
    cB
    c0
    opex
    @3
    @2
    cvv
    s2fv0
    ax-mp
    3eqtr3g
    @0
    @1
    wa
    @4
    @5
    c0
    c0
    wceq
    cA
    c0
    cB
    c0
    cI
    cvv
    opthg
    simprbda
    syl21anc
end
