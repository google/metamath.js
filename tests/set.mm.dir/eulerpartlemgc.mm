include "cn0.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "cin.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cbits.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "cmul.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "bitsss.mm"
include "simprr.mm"
include "sseldi.mm"
include "reexpcld.mm"
include "simprl.mm"
include "nnred.mm"
include "remulcld.mm"
include "wf.mm"
include "ccnv.mm"
include "cima.mm"
include "cfn.mm"
include "eulerpartlemelr.mm"
include "simpld.mm"
include "ffvelrnda.mm"
include "adantrr.mm"
include "nn0red.mm"
include "eulerpartlemsf.mm"
include "ffvelrni.mm"
include "adantr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "nnrpd.mm"
include "rprege0d.mm"
include "csn.mm"
include "csu.mm"
include "bitsfi.mm"
include "syl.mm"
include "wss.mm"
include "sselda.mm"
include "0le2.mm"
include "expge0d.mm"
include "snssd.mm"
include "fsumless.mm"
include "cc.mm"
include "wceq.mm"
include "recnd.mm"
include "oveq2.mm"
include "sumsn.mm"
include "syl2anc.mm"
include "bitsinv1.mm"
include "3brtr3d.mm"
include "lemul1a.mm"
include "syl31anc.mm"
include "c1.mm"
include "cfz.mm"
include "fzfid.mm"
include "elfznn.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "adantl.mm"
include "adantlr.mm"
include "nn0ge0d.mm"
include "0red.mm"
include "nngt0d.mm"
include "ltled.mm"
include "mulge0d.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "simpr.mm"
include "fsumge1.mm"
include "wn.mm"
include "cdif.mm"
include "eldif.mm"
include "caddc.mm"
include "cuz.mm"
include "wb.mm"
include "nndiffz1.mm"
include "eleq2d.mm"
include "pm5.32i.mm"
include "eulerpartlems.mm"
include "sylbi.mm"
include "oveq1d.mm"
include "eldifad.mm"
include "nncnd.mm"
include "mul02d.mm"
include "eqtrd.mm"
include "fsumge0.mm"
include "eqbrtrd.mm"
include "sylan2br.mm"
include "anassrs.mm"
include "pm2.61dan.mm"
include "eulerpartlemsv3.mm"
include "breqtrrd.mm"
include "letrd.mm"

theorem eulerpartlemgc
  let vt: setvar t
  let cA: class A
  let cR: class R
  let cS: class S
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vg: setvar g
  let vl: setvar l
  let vm: setvar m
  let vi: setvar i
  assume eulerpartlems.r: |- R = { f | ( `' f " NN ) e. Fin }
  assume eulerpartlems.s: |- S = ( f e. ( ( NN0 ^m NN ) i^i R ) |-> sum_ k e. NN ( ( f ` k ) x. k ) )

  disjoint f k
  disjoint A f
  disjoint A k
  disjoint R f
  disjoint R k
  disjoint k t
  disjoint A t
  disjoint R t
  disjoint S t
  disjoint S k
  disjoint f g
  disjoint g k
  disjoint R g
  disjoint k l
  disjoint k m
  disjoint l m
  disjoint l t
  disjoint A l
  disjoint m t
  disjoint A m
  disjoint R l
  disjoint S l
  disjoint i n
  disjoint i t
  disjoint A i
  disjoint R i
  assert |- ( ( A e. ( ( NN0 ^m NN ) i^i R ) /\ ( t e. NN /\ n e. ( bits ` ( A ` t ) ) ) ) -> ( ( 2 ^ n ) x. t ) <_ ( S ` A ) )

  proof
    cA
    cn0
    cn
    cmap
    co
    cR
    cin
    #
    wcel
    #
    vt
    cv
    #
    cn
    wcel
    #
    vn
    cv
    #
    @2
    cA
    cfv
    #
    cbits
    cfv
    #
    wcel
    #
    wa
    #
    wa
    #
    c2
    @4
    cexp
    co
    #
    @2
    cmul
    co
    #
    @5
    @2
    cmul
    co
    #
    cA
    cS
    cfv
    #
    @9
    @10
    @2
    @9
    c2
    @4
    c2
    cr
    wcel
    #
    @9
    2re
    a1i
    @9
    @6
    cn0
    @4
    @5
    bitsss
    #
    @1
    @3
    @7
    simprr
    #
    sseldi
    reexpcld
    #
    @9
    @2
    @1
    @3
    @7
    simprl
    #
    nnred
    #
    remulcld
    @9
    @5
    @2
    @9
    @5
    @1
    @3
    @5
    cn0
    wcel
    #
    @7
    @1
    cn
    cn0
    @2
    cA
    @1
    cn
    cn0
    cA
    wf
    #
    cA
    ccnv
    cn
    cima
    cfn
    wcel
    cA
    cR
    cS
    vf
    vk
    eulerpartlems.r
    eulerpartlems.s
    eulerpartlemelr
    simpld
    #
    ffvelrnda
    #
    adantrr
    #
    nn0red
    @19
    remulcld
    @9
    @13
    @1
    @13
    cn0
    wcel
    #
    @8
    @0
    cn0
    cA
    cS
    cR
    cS
    vf
    vk
    eulerpartlems.r
    eulerpartlems.s
    eulerpartlemsf
    ffvelrni
    #
    adantr
    nn0red
    @9
    @10
    cr
    wcel
    @5
    cr
    wcel
    #
    @2
    cr
    wcel
    cc0
    @2
    cle
    wbr
    wa
    @10
    @5
    cle
    wbr
    @11
    @12
    cle
    wbr
    @17
    @1
    @3
    @27
    @7
    @1
    @3
    wa
    #
    @5
    @23
    nn0red
    adantrr
    @9
    @2
    @9
    @2
    @18
    nnrpd
    rprege0d
    @9
    @4
    csn
    #
    c2
    vi
    cv
    #
    cexp
    co
    #
    vi
    csu
    #
    @6
    @31
    vi
    csu
    #
    @10
    @5
    cle
    @9
    @6
    @31
    @29
    vi
    @9
    @20
    @6
    cfn
    wcel
    @24
    @5
    bitsfi
    syl
    @9
    @30
    @6
    wcel
    wa
    #
    c2
    @30
    @14
    @34
    2re
    a1i
    #
    @9
    @6
    cn0
    @30
    @6
    cn0
    wss
    @9
    @15
    a1i
    sselda
    #
    reexpcld
    @34
    c2
    @30
    @35
    @36
    cc0
    c2
    cle
    wbr
    @34
    0le2
    a1i
    expge0d
    @9
    @4
    @6
    @16
    snssd
    fsumless
    @9
    @7
    @10
    cc
    wcel
    @32
    @10
    wceq
    @16
    @9
    @10
    @17
    recnd
    @31
    @10
    vi
    @4
    @6
    @30
    @4
    c2
    cexp
    oveq2
    sumsn
    syl2anc
    @9
    @20
    @33
    @5
    wceq
    @24
    vi
    @5
    bitsinv1
    syl
    3brtr3d
    @10
    @5
    @2
    lemul1a
    syl31anc
    @1
    @3
    @12
    @13
    cle
    wbr
    @7
    @28
    @12
    c1
    @13
    cfz
    co
    #
    vk
    cv
    #
    cA
    cfv
    #
    @38
    cmul
    co
    #
    vk
    csu
    #
    @13
    cle
    @28
    @2
    @37
    wcel
    #
    @12
    @41
    cle
    wbr
    #
    @1
    @42
    @43
    @3
    @1
    @42
    wa
    #
    @37
    @40
    @12
    vk
    @2
    @44
    c1
    @13
    fzfid
    @1
    @38
    @37
    wcel
    #
    @40
    cr
    wcel
    @42
    @1
    @45
    wa
    #
    @39
    @38
    @46
    @39
    @1
    @21
    @38
    cn
    wcel
    #
    @39
    cn0
    wcel
    @45
    @22
    @38
    @13
    elfznn
    #
    cn
    cn0
    @38
    cA
    ffvelrn
    syl2an
    #
    nn0red
    #
    @46
    @38
    @45
    @47
    @1
    @48
    adantl
    #
    nnred
    #
    remulcld
    #
    adantlr
    @1
    @45
    cc0
    @40
    cle
    wbr
    @42
    @46
    @39
    @38
    @50
    @52
    @46
    @39
    @49
    nn0ge0d
    @46
    cc0
    @38
    @46
    0red
    @52
    @46
    @38
    @51
    nngt0d
    ltled
    mulge0d
    #
    adantlr
    @38
    @2
    wceq
    #
    @39
    @5
    @38
    @2
    cmul
    @38
    @2
    cA
    fveq2
    @55
    id
    oveq12d
    @1
    @42
    simpr
    fsumge1
    adantlr
    @1
    @3
    @42
    wn
    #
    @43
    @3
    @56
    wa
    @1
    @2
    cn
    @37
    cdif
    #
    wcel
    #
    @43
    @2
    cn
    @37
    eldif
    @1
    @58
    wa
    #
    @12
    cc0
    @41
    cle
    @59
    @12
    cc0
    @2
    cmul
    co
    cc0
    @59
    @5
    cc0
    @2
    cmul
    @59
    @1
    @2
    @13
    c1
    caddc
    co
    cuz
    cfv
    #
    wcel
    #
    wa
    @5
    cc0
    wceq
    @1
    @58
    @61
    @1
    @25
    @58
    @61
    wb
    @26
    @25
    @57
    @60
    @2
    @13
    nndiffz1
    eleq2d
    syl
    pm5.32i
    vt
    cA
    cR
    cS
    vf
    vk
    eulerpartlems.r
    eulerpartlems.s
    eulerpartlems
    sylbi
    oveq1d
    @59
    @2
    @59
    @2
    @59
    @2
    cn
    @37
    @1
    @58
    simpr
    eldifad
    nncnd
    mul02d
    eqtrd
    @1
    cc0
    @41
    cle
    wbr
    @58
    @1
    @37
    @40
    vk
    @1
    c1
    @13
    fzfid
    @53
    @54
    fsumge0
    adantr
    eqbrtrd
    sylan2br
    anassrs
    pm2.61dan
    @1
    @13
    @41
    wceq
    @3
    cA
    cR
    cS
    vf
    vk
    eulerpartlems.r
    eulerpartlems.s
    eulerpartlemsv3
    adantr
    breqtrrd
    adantrr
    letrd
end
