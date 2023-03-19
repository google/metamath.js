include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "w3a.mm"
include "cz.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wf1o.mm"
include "wceq.mm"
include "cn.mm"
include "weq.mm"
include "wi.mm"
include "3simpb.mm"
include "reximi.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "seqeq1.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "reeanv.mm"
include "wcel.mm"
include "simprlr.mm"
include "chash.mm"
include "clt.mm"
include "wiso.mm"
include "wor.mm"
include "cfn.mm"
include "cr.mm"
include "simprll.mm"
include "uzssz.mm"
include "zssre.mm"
include "sstri.mm"
include "syl6ss.mm"
include "ltso.mm"
include "soss.mm"
include "mpisyl.mm"
include "cen.mm"
include "fzfi.mm"
include "ovex.mm"
include "f1oen.mm"
include "ad2antll.mm"
include "ensymd.mm"
include "enfii.mm"
include "sylancr.mm"
include "fz1iso.mm"
include "syl2anc.mm"
include "csb.mm"
include "cmpt.mm"
include "cc.mm"
include "simpll.mm"
include "sylan.mm"
include "eqid.mm"
include "simplrr.mm"
include "simplrl.mm"
include "simplll.mm"
include "adantl.mm"
include "simprr.mm"
include "prodmolem2a.mm"
include "expr.mm"
include "exlimdv.mm"
include "mpd.mm"
include "climuni.mm"
include "eqeq2.mm"
include "syl5ibrcom.mm"
include "impd.mm"
include "expimpd.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "expdimp.mm"
include "sylan2b.mm"
include "sylan2.mm"

theorem prodmolem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vg: setvar g
  let vw: setvar w
  let cM: class M
  let cN: class N
  assume prodmo.1: |- F = ( k e. ZZ |-> if ( k e. A , B , 1 ) )
  assume prodmo.2: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume prodmo.3: |- G = ( j e. NN |-> [_ ( f ` j ) / k ]_ B )

  disjoint A f
  disjoint A j
  disjoint A m
  disjoint B j
  disjoint F f
  disjoint f j
  disjoint F j
  disjoint f k
  disjoint f m
  disjoint F m
  disjoint f ph
  disjoint f x
  disjoint f z
  disjoint G j
  disjoint j k
  disjoint j m
  disjoint j ph
  disjoint j x
  disjoint k m
  disjoint k x
  disjoint m ph
  disjoint m x
  disjoint m z
  disjoint A k
  disjoint A n
  disjoint k n
  disjoint F k
  disjoint F n
  disjoint k ph
  disjoint n ph
  disjoint A g
  disjoint A w
  disjoint f g
  disjoint F g
  disjoint f w
  disjoint F w
  disjoint G g
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g ph
  disjoint g w
  disjoint G w
  disjoint g x
  disjoint j w
  disjoint k w
  disjoint m w
  disjoint ph w
  disjoint w x
  disjoint w z
  disjoint M n
  disjoint N n
  assert |- ( ( ph /\ E. m e. ZZ ( A C_ ( ZZ>= ` m ) /\ E. n e. ( ZZ>= ` m ) E. y ( y =/= 0 /\ seq n ( x. , F ) ~~> y ) /\ seq m ( x. , F ) ~~> x ) ) -> ( E. m e. NN E. f ( f : ( 1 ... m ) -1-1-onto-> A /\ z = ( seq 1 ( x. , G ) ` m ) ) -> x = z ) )

  proof
    cA
    vm
    cv
    #
    cuz
    cfv
    #
    wss
    #
    vy
    cv
    #
    cc0
    wne
    cmul
    cF
    vn
    cv
    cseq
    @3
    cli
    wbr
    wa
    vy
    wex
    vn
    @1
    wrex
    #
    cmul
    cF
    @0
    cseq
    #
    vx
    cv
    #
    cli
    wbr
    #
    w3a
    #
    vm
    cz
    wrex
    wph
    @2
    @7
    wa
    #
    vm
    cz
    wrex
    #
    c1
    @0
    cfz
    co
    #
    cA
    vf
    cv
    #
    wf1o
    #
    vz
    cv
    #
    @0
    cmul
    cG
    c1
    cseq
    cfv
    #
    wceq
    #
    wa
    #
    vf
    wex
    #
    vm
    cn
    wrex
    #
    vx
    vz
    weq
    #
    wi
    #
    @8
    @9
    vm
    cz
    @2
    @4
    @7
    3simpb
    reximi
    @10
    wph
    cA
    vw
    cv
    #
    cuz
    cfv
    #
    wss
    #
    cmul
    cF
    @22
    cseq
    #
    @6
    cli
    wbr
    #
    wa
    #
    vw
    cz
    wrex
    #
    @21
    @9
    @27
    vm
    vw
    cz
    vm
    vw
    weq
    #
    @2
    @24
    @7
    @26
    @29
    @1
    @23
    cA
    @0
    @22
    cuz
    fveq2
    sseq2d
    @29
    @5
    @25
    @6
    cli
    cmul
    cF
    @0
    @22
    seqeq1
    breq1d
    anbi12d
    cbvrexv
    wph
    @28
    @19
    @20
    @28
    @19
    wa
    @27
    @18
    wa
    #
    vm
    cn
    wrex
    vw
    cz
    wrex
    wph
    @20
    @27
    @18
    vw
    vm
    cz
    cn
    reeanv
    wph
    @30
    @20
    vw
    vm
    cz
    cn
    wph
    @22
    cz
    wcel
    #
    @0
    cn
    wcel
    #
    wa
    #
    wa
    #
    @27
    @18
    @20
    @34
    @27
    wa
    #
    @17
    @20
    vf
    @35
    @13
    @16
    @20
    @34
    @27
    @13
    @16
    @20
    wi
    @34
    @27
    @13
    wa
    #
    wa
    #
    @20
    @16
    @6
    @15
    wceq
    #
    @37
    @26
    @25
    @15
    cli
    wbr
    #
    @38
    @34
    @24
    @26
    @13
    simprlr
    @37
    c1
    cA
    chash
    cfv
    cfz
    co
    cA
    clt
    clt
    vg
    cv
    #
    wiso
    #
    vg
    wex
    #
    @39
    @37
    cA
    clt
    wor
    #
    cA
    cfn
    wcel
    #
    @42
    @37
    cA
    cr
    wss
    cr
    clt
    wor
    @43
    @37
    cA
    @23
    cr
    @34
    @24
    @26
    @13
    simprll
    @23
    cz
    cr
    @22
    uzssz
    zssre
    sstri
    syl6ss
    ltso
    cA
    cr
    clt
    soss
    mpisyl
    @37
    @11
    cfn
    wcel
    cA
    @11
    cen
    wbr
    @44
    c1
    @0
    fzfi
    @37
    @11
    cA
    @13
    @11
    cA
    cen
    wbr
    @34
    @27
    @11
    cA
    @12
    c1
    @0
    cfz
    ovex
    f1oen
    ad2antll
    ensymd
    cA
    @11
    enfii
    sylancr
    cA
    clt
    vg
    fz1iso
    syl2anc
    @37
    @41
    @39
    vg
    @34
    @36
    @41
    @39
    @34
    @36
    @41
    wa
    #
    wa
    #
    cA
    cB
    vf
    vj
    vk
    cF
    cG
    vj
    cn
    vk
    vj
    cv
    @40
    cfv
    cB
    csb
    cmpt
    #
    @40
    @22
    @0
    prodmo.1
    @46
    wph
    vk
    cv
    cA
    wcel
    cB
    cc
    wcel
    wph
    @33
    @45
    simpll
    prodmo.2
    sylan
    prodmo.3
    @47
    eqid
    wph
    @31
    @32
    @45
    simplrr
    wph
    @31
    @32
    @45
    simplrl
    @45
    @24
    @34
    @24
    @26
    @13
    @41
    simplll
    adantl
    @34
    @27
    @13
    @41
    simprlr
    @34
    @36
    @41
    simprr
    prodmolem2a
    expr
    exlimdv
    mpd
    @6
    @15
    @25
    climuni
    syl2anc
    @14
    @15
    @6
    eqeq2
    syl5ibrcom
    expr
    impd
    exlimdv
    expimpd
    rexlimdvva
    syl5bir
    expdimp
    sylan2b
    sylan2
end
