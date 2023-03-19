include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "wa.mm"
include "cz.mm"
include "wrex.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wf1o.mm"
include "wceq.mm"
include "wex.mm"
include "cn.mm"
include "wi.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "seqeq1.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "wcel.mm"
include "simplrr.mm"
include "chash.mm"
include "clt.mm"
include "wiso.mm"
include "wor.mm"
include "cfn.mm"
include "cr.mm"
include "simplrl.mm"
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
include "simplll.mm"
include "sylan.mm"
include "eqid.mm"
include "simprll.mm"
include "simpllr.mm"
include "simprlr.mm"
include "simprr.mm"
include "summolem2a.mm"
include "expr.mm"
include "exlimdv.mm"
include "mpd.mm"
include "climuni.mm"
include "anassrs.mm"
include "eqeq2.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "rexlimdva.mm"
include "r19.29an.mm"
include "sylan2b.mm"

theorem summolem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let cH: class H
  let cK: class K
  let cN: class N
  let cM: class M
  assume summo.1: |- F = ( k e. ZZ |-> if ( k e. A , B , 0 ) )
  assume summo.2: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume summo.3: |- G = ( n e. NN |-> [_ ( f ` n ) / k ]_ B )

  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F f
  disjoint F k
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint G k
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph y
  disjoint B f
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint f ph
  disjoint f g
  disjoint f i
  disjoint f j
  disjoint g i
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint A i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint A j
  disjoint F g
  disjoint F j
  disjoint G g
  disjoint G i
  disjoint G j
  disjoint H i
  disjoint H x
  disjoint K i
  disjoint K j
  disjoint K k
  disjoint K m
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint N k
  disjoint N m
  disjoint N n
  disjoint g ph
  disjoint i ph
  disjoint j ph
  disjoint B j
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint M m
  disjoint M n
  disjoint M x
  disjoint M y
  assert |- ( ( ph /\ E. m e. ZZ ( A C_ ( ZZ>= ` m ) /\ seq m ( + , F ) ~~> x ) ) -> ( E. m e. NN E. f ( f : ( 1 ... m ) -1-1-onto-> A /\ y = ( seq 1 ( + , G ) ` m ) ) -> x = y ) )

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
    caddc
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
    wa
    #
    vm
    cz
    wrex
    wph
    cA
    vj
    cv
    #
    cuz
    cfv
    #
    wss
    #
    caddc
    cF
    @7
    cseq
    #
    @4
    cli
    wbr
    #
    wa
    #
    vj
    cz
    wrex
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
    vy
    cv
    #
    @0
    caddc
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
    @4
    @16
    wceq
    #
    wi
    #
    @6
    @12
    vm
    vj
    cz
    @0
    @7
    wceq
    #
    @2
    @9
    @5
    @11
    @23
    @1
    @8
    cA
    @0
    @7
    cuz
    fveq2
    sseq2d
    @23
    @3
    @10
    @4
    cli
    caddc
    cF
    @0
    @7
    seqeq1
    breq1d
    anbi12d
    cbvrexv
    wph
    @12
    @22
    vj
    cz
    wph
    @7
    cz
    wcel
    #
    wa
    #
    @12
    wa
    #
    @20
    @21
    vm
    cn
    @26
    @0
    cn
    wcel
    #
    wa
    #
    @19
    @21
    vf
    @28
    @15
    @18
    @21
    @28
    @15
    wa
    @21
    @18
    @4
    @17
    wceq
    #
    @26
    @27
    @15
    @29
    @26
    @27
    @15
    wa
    #
    wa
    #
    @11
    @10
    @17
    cli
    wbr
    #
    @29
    @25
    @9
    @11
    @30
    simplrr
    @31
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
    @32
    @31
    cA
    clt
    wor
    #
    cA
    cfn
    wcel
    #
    @35
    @31
    cA
    cr
    wss
    cr
    clt
    wor
    @36
    @31
    cA
    @8
    cr
    @25
    @9
    @11
    @30
    simplrl
    @8
    cz
    cr
    @7
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
    @31
    @13
    cfn
    wcel
    cA
    @13
    cen
    wbr
    @37
    c1
    @0
    fzfi
    @31
    @13
    cA
    @15
    @13
    cA
    cen
    wbr
    @26
    @27
    @13
    cA
    @14
    c1
    @0
    cfz
    ovex
    f1oen
    ad2antll
    ensymd
    cA
    @13
    enfii
    sylancr
    cA
    clt
    vg
    fz1iso
    syl2anc
    @31
    @34
    @32
    vg
    @26
    @30
    @34
    @32
    @26
    @30
    @34
    wa
    #
    wa
    #
    cA
    cB
    vf
    vk
    vn
    cF
    cG
    vn
    cn
    vk
    vn
    cv
    @33
    cfv
    cB
    csb
    cmpt
    #
    @33
    @7
    @0
    summo.1
    @39
    wph
    vk
    cv
    cA
    wcel
    cB
    cc
    wcel
    wph
    @24
    @12
    @38
    simplll
    summo.2
    sylan
    summo.3
    @40
    eqid
    @26
    @27
    @15
    @34
    simprll
    wph
    @24
    @12
    @38
    simpllr
    @25
    @9
    @11
    @38
    simplrl
    @26
    @27
    @15
    @34
    simprlr
    @26
    @30
    @34
    simprr
    summolem2a
    expr
    exlimdv
    mpd
    @4
    @17
    @10
    climuni
    syl2anc
    anassrs
    @16
    @17
    @4
    eqeq2
    syl5ibrcom
    expimpd
    exlimdv
    rexlimdva
    r19.29an
    sylan2b
end
