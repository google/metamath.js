include "csmu.mm"
include "co.mm"
include "cc0.mm"
include "cfzo.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "cfv.mm"
include "cn0.mm"
include "wss.mm"
include "adantr.mm"
include "cuz.mm"
include "elfzouz.mm"
include "adantl.mm"
include "nn0uz.mm"
include "syl6eleqr.mm"
include "c1.mm"
include "caddc.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "nn0zd.mm"
include "peano2zd.mm"
include "clt.mm"
include "elfzolt2.mm"
include "nn0ltp1le.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "smuval2.mm"
include "wceq.mm"
include "cfz.mm"
include "syl6eleq.mm"
include "eluzfz2b.mm"
include "sylib.mm"
include "wi.mm"
include "fveq2.mm"
include "ineq1d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "c0.mm"
include "smup0.mm"
include "inss1.mm"
include "syl5ss.mm"
include "eqtr4d.mm"
include "a1i.mm"
include "cmin.mm"
include "crab.mm"
include "csad.mm"
include "oveq1.mm"
include "elfzonn0.mm"
include "smupp1.mm"
include "cpw.mm"
include "wf.mm"
include "smupf.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "elpwid.mm"
include "ssrab2.mm"
include "sadeq.mm"
include "eqtrd.mm"
include "inss2.mm"
include "sseli.mm"
include "sseld.mm"
include "cn.mm"
include "elfzo0.mm"
include "simp2bi.mm"
include "nn0red.mm"
include "resubcld.mm"
include "nnred.mm"
include "nn0ge0d.mm"
include "subge02d.mm"
include "lelttrd.mm"
include "jca.mm"
include "w3a.mm"
include "3anass.mm"
include "bitri.mm"
include "baib.mm"
include "syl5ibrcom.mm"
include "syld.mm"
include "pm4.71rd.mm"
include "ancom.mm"
include "elin.mm"
include "bitr4i.mm"
include "syl6rbb.mm"
include "anbi2d.mm"
include "sylan2.mm"
include "rabbidva.mm"
include "inrab2.mm"
include "3eqtr4g.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "a2d.mm"
include "fzind2.mm"
include "mpcom.mm"
include "eleq2d.mm"
include "rbaib.mm"
include "3bitr3d.mm"
include "smupval.mm"
include "3bitrd.mm"
include "ex.mm"
include "pm5.32rd.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem smueqlem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let vm: setvar m
  let vn: setvar n
  let cN: class N
  let vp: setvar p
  let vk: setvar k
  let vi: setvar i
  let vx: setvar x
  assume smueq.a: |- ( ph -> A C_ NN0 )
  assume smueq.b: |- ( ph -> B C_ NN0 )
  assume smueq.n: |- ( ph -> N e. NN0 )
  assume smueq.p: |- P = seq 0 ( ( p e. ~P NN0 , m e. NN0 |-> ( p sadd { n e. NN0 | ( m e. A /\ ( n - m ) e. B ) } ) ) , ( n e. NN0 |-> if ( n = 0 , (/) , ( n - 1 ) ) ) )
  assume smueq.q: |- Q = seq 0 ( ( p e. ~P NN0 , m e. NN0 |-> ( p sadd { n e. NN0 | ( m e. A /\ ( n - m ) e. ( B i^i ( 0 ..^ N ) ) ) } ) ) , ( n e. NN0 |-> if ( n = 0 , (/) , ( n - 1 ) ) ) )

  disjoint m n
  disjoint m p
  disjoint A m
  disjoint n p
  disjoint A n
  disjoint A p
  disjoint B m
  disjoint B n
  disjoint B p
  disjoint N m
  disjoint N n
  disjoint N p
  disjoint n ph
  disjoint k m
  disjoint k n
  disjoint k p
  disjoint A k
  disjoint B k
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i p
  disjoint i x
  disjoint N i
  disjoint k x
  disjoint N k
  disjoint m x
  disjoint n x
  disjoint p x
  disjoint N x
  disjoint i ph
  disjoint k ph
  disjoint ph x
  disjoint P i
  disjoint P x
  disjoint Q i
  disjoint Q x
  assert |- ( ph -> ( ( A smul B ) i^i ( 0 ..^ N ) ) = ( ( ( A i^i ( 0 ..^ N ) ) smul ( B i^i ( 0 ..^ N ) ) ) i^i ( 0 ..^ N ) ) )

  proof
    wph
    vk
    cA
    cB
    csmu
    co
    #
    cc0
    cN
    cfzo
    co
    #
    cin
    #
    cA
    @1
    cin
    cB
    @1
    cin
    #
    csmu
    co
    #
    @1
    cin
    #
    wph
    vk
    cv
    #
    @0
    wcel
    #
    @6
    @1
    wcel
    #
    wa
    @6
    @4
    wcel
    #
    @8
    wa
    @6
    @2
    wcel
    @6
    @5
    wcel
    wph
    @8
    @7
    @9
    wph
    @8
    @7
    @9
    wb
    wph
    @8
    wa
    #
    @7
    @6
    cN
    cP
    cfv
    #
    wcel
    #
    @6
    cN
    cQ
    cfv
    #
    wcel
    #
    @9
    @10
    cA
    cB
    cP
    vm
    vn
    cN
    @6
    vp
    wph
    cA
    cn0
    wss
    #
    @8
    smueq.a
    adantr
    #
    wph
    cB
    cn0
    wss
    #
    @8
    smueq.b
    adantr
    smueq.p
    @10
    @6
    cc0
    cuz
    cfv
    #
    cn0
    @8
    @6
    @18
    wcel
    wph
    @6
    cc0
    cN
    elfzouz
    adantl
    nn0uz
    syl6eleqr
    #
    @10
    @6
    c1
    caddc
    co
    #
    cz
    wcel
    cN
    cz
    wcel
    @20
    cN
    cle
    wbr
    #
    cN
    @20
    cuz
    cfv
    wcel
    @10
    @6
    @10
    @6
    @19
    nn0zd
    peano2zd
    @10
    cN
    wph
    cN
    cn0
    wcel
    #
    @8
    smueq.n
    adantr
    #
    nn0zd
    @10
    @6
    cN
    clt
    wbr
    #
    @21
    @8
    @24
    wph
    @6
    cc0
    cN
    elfzolt2
    adantl
    @10
    @6
    cn0
    wcel
    @22
    @24
    @21
    wb
    @19
    @23
    @6
    cN
    nn0ltp1le
    syl2anc
    mpbid
    @20
    cN
    eluz2
    syl3anbrc
    smuval2
    @10
    @6
    @11
    @1
    cin
    #
    wcel
    #
    @6
    @13
    @1
    cin
    #
    wcel
    #
    @12
    @14
    @10
    @25
    @27
    @6
    wph
    @25
    @27
    wceq
    #
    @8
    cN
    cc0
    cN
    cfz
    co
    wcel
    #
    wph
    @29
    wph
    cN
    @18
    wcel
    #
    @30
    wph
    cN
    cn0
    @18
    smueq.n
    nn0uz
    syl6eleq
    cc0
    cN
    eluzfz2b
    sylib
    wph
    vx
    cv
    #
    cP
    cfv
    #
    @1
    cin
    #
    @32
    cQ
    cfv
    #
    @1
    cin
    #
    wceq
    #
    wi
    wph
    cc0
    cP
    cfv
    #
    @1
    cin
    #
    cc0
    cQ
    cfv
    #
    @1
    cin
    #
    wceq
    #
    wi
    #
    wph
    vi
    cv
    #
    cP
    cfv
    #
    @1
    cin
    #
    @44
    cQ
    cfv
    #
    @1
    cin
    #
    wceq
    #
    wi
    wph
    @44
    c1
    caddc
    co
    #
    cP
    cfv
    #
    @1
    cin
    #
    @50
    cQ
    cfv
    #
    @1
    cin
    #
    wceq
    #
    wi
    wph
    @29
    wi
    vx
    vi
    cN
    cc0
    cN
    @32
    cc0
    wceq
    #
    @37
    @42
    wph
    @56
    @34
    @39
    @36
    @41
    @56
    @33
    @38
    @1
    @32
    cc0
    cP
    fveq2
    ineq1d
    @56
    @35
    @40
    @1
    @32
    cc0
    cQ
    fveq2
    ineq1d
    eqeq12d
    imbi2d
    @32
    @44
    wceq
    #
    @37
    @49
    wph
    @57
    @34
    @46
    @36
    @48
    @57
    @33
    @45
    @1
    @32
    @44
    cP
    fveq2
    ineq1d
    @57
    @35
    @47
    @1
    @32
    @44
    cQ
    fveq2
    ineq1d
    eqeq12d
    imbi2d
    @32
    @50
    wceq
    #
    @37
    @55
    wph
    @58
    @34
    @52
    @36
    @54
    @58
    @33
    @51
    @1
    @32
    @50
    cP
    fveq2
    ineq1d
    @58
    @35
    @53
    @1
    @32
    @50
    cQ
    fveq2
    ineq1d
    eqeq12d
    imbi2d
    @32
    cN
    wceq
    #
    @37
    @29
    wph
    @59
    @34
    @25
    @36
    @27
    @59
    @33
    @11
    @1
    @32
    cN
    cP
    fveq2
    ineq1d
    @59
    @35
    @13
    @1
    @32
    cN
    cQ
    fveq2
    ineq1d
    eqeq12d
    imbi2d
    @43
    @31
    wph
    @38
    @40
    @1
    wph
    @38
    c0
    @40
    wph
    cA
    cB
    cP
    vm
    vn
    vp
    smueq.a
    smueq.b
    smueq.p
    smup0
    wph
    cA
    @3
    cQ
    vm
    vn
    vp
    smueq.a
    wph
    @3
    cB
    cn0
    cB
    @1
    inss1
    smueq.b
    syl5ss
    #
    smueq.q
    smup0
    eqtr4d
    ineq1d
    a1i
    @44
    @1
    wcel
    #
    wph
    @49
    @55
    wph
    @61
    @49
    @55
    wi
    @49
    @55
    wph
    @61
    wa
    #
    @46
    @44
    cA
    wcel
    #
    vn
    cv
    #
    @44
    cmin
    co
    #
    cB
    wcel
    #
    wa
    #
    vn
    cn0
    crab
    #
    @1
    cin
    #
    csad
    co
    #
    @1
    cin
    #
    @48
    @69
    csad
    co
    #
    @1
    cin
    #
    wceq
    @49
    @70
    @72
    @1
    @46
    @48
    @69
    csad
    oveq1
    ineq1d
    @62
    @52
    @71
    @54
    @73
    @62
    @52
    @45
    @68
    csad
    co
    #
    @1
    cin
    @71
    @62
    @51
    @74
    @1
    @62
    cA
    cB
    cP
    vm
    vn
    @44
    vp
    wph
    @15
    @61
    smueq.a
    adantr
    #
    wph
    @17
    @61
    smueq.b
    adantr
    #
    smueq.p
    @61
    @44
    cn0
    wcel
    #
    wph
    @44
    cN
    elfzonn0
    #
    adantl
    #
    smupp1
    ineq1d
    @62
    @45
    @68
    cN
    @62
    @45
    cn0
    wph
    cn0
    cn0
    cpw
    #
    cP
    wf
    @77
    @45
    @80
    wcel
    @61
    wph
    cA
    cB
    cP
    vm
    vn
    vp
    smueq.a
    smueq.b
    smueq.p
    smupf
    @78
    cn0
    @80
    @44
    cP
    ffvelrn
    syl2an
    elpwid
    @68
    cn0
    wss
    @62
    @67
    vn
    cn0
    ssrab2
    a1i
    wph
    @22
    @61
    smueq.n
    adantr
    #
    sadeq
    eqtrd
    @62
    @54
    @47
    @63
    @65
    @3
    wcel
    #
    wa
    #
    vn
    cn0
    crab
    #
    csad
    co
    #
    @1
    cin
    @48
    @84
    @1
    cin
    #
    csad
    co
    #
    @1
    cin
    @73
    @62
    @53
    @85
    @1
    @62
    cA
    @3
    cQ
    vm
    vn
    @44
    vp
    @75
    wph
    @3
    cn0
    wss
    #
    @61
    @60
    adantr
    smueq.q
    @79
    smupp1
    ineq1d
    @62
    @47
    @84
    cN
    @62
    @47
    cn0
    wph
    cn0
    @80
    cQ
    wf
    @77
    @47
    @80
    wcel
    @61
    wph
    cA
    @3
    cQ
    vm
    vn
    vp
    smueq.a
    @60
    smueq.q
    smupf
    @78
    cn0
    @80
    @44
    cQ
    ffvelrn
    syl2an
    elpwid
    @84
    cn0
    wss
    @62
    @83
    vn
    cn0
    ssrab2
    a1i
    @81
    sadeq
    @62
    @87
    @72
    @1
    @62
    @86
    @69
    @48
    csad
    @62
    @83
    vn
    cn0
    @1
    cin
    #
    crab
    @67
    vn
    @89
    crab
    @86
    @69
    @62
    @83
    @67
    vn
    @89
    @64
    @89
    wcel
    @62
    @64
    @1
    wcel
    #
    @83
    @67
    wb
    @89
    @1
    @64
    cn0
    @1
    inss2
    sseli
    @62
    @90
    wa
    #
    @82
    @66
    @63
    @91
    @66
    @65
    @1
    wcel
    #
    @66
    wa
    #
    @82
    @91
    @66
    @92
    @91
    @66
    @65
    cn0
    wcel
    #
    @92
    @91
    cB
    cn0
    @65
    @62
    @17
    @90
    @76
    adantr
    sseld
    @91
    @92
    @94
    cN
    cn
    wcel
    #
    @65
    cN
    clt
    wbr
    #
    wa
    #
    @91
    @95
    @96
    @90
    @95
    @62
    @90
    @64
    cn0
    wcel
    #
    @95
    @64
    cN
    clt
    wbr
    #
    @64
    cN
    elfzo0
    simp2bi
    adantl
    #
    @91
    @65
    @64
    cN
    @91
    @64
    @44
    @91
    @64
    @90
    @98
    @62
    @64
    cN
    elfzonn0
    adantl
    nn0red
    #
    @91
    @44
    @62
    @77
    @90
    @79
    adantr
    #
    nn0red
    #
    resubcld
    @101
    @91
    cN
    @100
    nnred
    @91
    cc0
    @44
    cle
    wbr
    @65
    @64
    cle
    wbr
    @91
    @44
    @102
    nn0ge0d
    @91
    @64
    @44
    @101
    @103
    subge02d
    mpbid
    @90
    @99
    @62
    @64
    cc0
    cN
    elfzolt2
    adantl
    lelttrd
    jca
    @92
    @94
    @97
    @92
    @94
    @95
    @96
    w3a
    @94
    @97
    wa
    @65
    cN
    elfzo0
    @94
    @95
    @96
    3anass
    bitri
    baib
    syl5ibrcom
    syld
    pm4.71rd
    @93
    @66
    @92
    wa
    @82
    @92
    @66
    ancom
    @65
    cB
    @1
    elin
    bitr4i
    syl6rbb
    anbi2d
    sylan2
    rabbidva
    @83
    vn
    cn0
    @1
    inrab2
    @67
    vn
    cn0
    @1
    inrab2
    3eqtr4g
    oveq2d
    ineq1d
    3eqtrd
    eqeq12d
    syl5ibr
    expcom
    a2d
    fzind2
    mpcom
    adantr
    eleq2d
    @8
    @26
    @12
    wb
    wph
    @26
    @12
    @8
    @6
    @11
    @1
    elin
    rbaib
    adantl
    @8
    @28
    @14
    wb
    wph
    @28
    @14
    @8
    @6
    @13
    @1
    elin
    rbaib
    adantl
    3bitr3d
    @10
    @13
    @4
    @6
    @10
    cA
    @3
    cQ
    vm
    vn
    cN
    vp
    @16
    wph
    @88
    @8
    @60
    adantr
    smueq.q
    @23
    smupval
    eleq2d
    3bitrd
    ex
    pm5.32rd
    @6
    @0
    @1
    elin
    @6
    @4
    @1
    elin
    3bitr4g
    eqrdv
end
