include "cfv.mm"
include "cn0.mm"
include "cpw.mm"
include "cv.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cin.mm"
include "wcel.mm"
include "cmin.mm"
include "wa.mm"
include "crab.mm"
include "csad.mm"
include "cmpt2.mm"
include "wceq.mm"
include "c0.mm"
include "c1.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "csmu.mm"
include "cfz.mm"
include "cuz.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eluzfz2b.mm"
include "sylib.mm"
include "wi.mm"
include "caddc.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "smup0.mm"
include "inss1.mm"
include "syl5ss.mm"
include "eqid.mm"
include "eqtr4d.mm"
include "a1i.mm"
include "oveq1.mm"
include "wss.mm"
include "adantr.mm"
include "elfzouz.mm"
include "adantl.mm"
include "syl6eleqr.mm"
include "smupp1.mm"
include "wb.mm"
include "elin.mm"
include "rbaib.mm"
include "anbi1d.mm"
include "rabbidv.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "a2d.mm"
include "fzind2.mm"
include "mpcom.mm"
include "inss2.mm"
include "cz.mm"
include "nn0zd.mm"
include "uzid.mm"
include "syl.mm"
include "smupvallem.mm"

theorem smupval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let vm: setvar m
  let vn: setvar n
  let cN: class N
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x
  assume smupval.a: |- ( ph -> A C_ NN0 )
  assume smupval.b: |- ( ph -> B C_ NN0 )
  assume smupval.p: |- P = seq 0 ( ( p e. ~P NN0 , m e. NN0 |-> ( p sadd { n e. NN0 | ( m e. A /\ ( n - m ) e. B ) } ) ) , ( n e. NN0 |-> if ( n = 0 , (/) , ( n - 1 ) ) ) )
  assume smupval.n: |- ( ph -> N e. NN0 )

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
  disjoint k x
  disjoint A k
  disjoint m x
  disjoint n x
  disjoint p x
  disjoint A x
  disjoint B k
  disjoint B x
  disjoint N k
  disjoint N x
  disjoint k ph
  disjoint ph x
  disjoint P k
  disjoint P x
  assert |- ( ph -> ( P ` N ) = ( ( A i^i ( 0 ..^ N ) ) smul B ) )

  proof
    wph
    cN
    cP
    cfv
    #
    cN
    vp
    vm
    cn0
    cpw
    cn0
    vp
    cv
    vm
    cv
    #
    cA
    cc0
    cN
    cfzo
    co
    #
    cin
    #
    wcel
    vn
    cv
    #
    @1
    cmin
    co
    cB
    wcel
    wa
    vn
    cn0
    crab
    csad
    co
    cmpt2
    vn
    cn0
    @4
    cc0
    wceq
    c0
    @4
    c1
    cmin
    co
    cif
    cmpt
    cc0
    cseq
    #
    cfv
    #
    @3
    cB
    csmu
    co
    cN
    cc0
    cN
    cfz
    co
    wcel
    #
    wph
    @0
    @6
    wceq
    #
    wph
    cN
    cc0
    cuz
    cfv
    #
    wcel
    #
    @7
    wph
    cN
    cn0
    @9
    smupval.n
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
    @11
    @5
    cfv
    #
    wceq
    #
    wi
    wph
    cc0
    cP
    cfv
    #
    cc0
    @5
    cfv
    #
    wceq
    #
    wi
    #
    wph
    vk
    cv
    #
    cP
    cfv
    #
    @19
    @5
    cfv
    #
    wceq
    #
    wi
    wph
    @19
    c1
    caddc
    co
    #
    cP
    cfv
    #
    @23
    @5
    cfv
    #
    wceq
    #
    wi
    wph
    @8
    wi
    vx
    vk
    cN
    cc0
    cN
    @11
    cc0
    wceq
    #
    @14
    @17
    wph
    @27
    @12
    @15
    @13
    @16
    @11
    cc0
    cP
    fveq2
    @11
    cc0
    @5
    fveq2
    eqeq12d
    imbi2d
    @11
    @19
    wceq
    #
    @14
    @22
    wph
    @28
    @12
    @20
    @13
    @21
    @11
    @19
    cP
    fveq2
    @11
    @19
    @5
    fveq2
    eqeq12d
    imbi2d
    @11
    @23
    wceq
    #
    @14
    @26
    wph
    @29
    @12
    @24
    @13
    @25
    @11
    @23
    cP
    fveq2
    @11
    @23
    @5
    fveq2
    eqeq12d
    imbi2d
    @11
    cN
    wceq
    #
    @14
    @8
    wph
    @30
    @12
    @0
    @13
    @6
    @11
    cN
    cP
    fveq2
    @11
    cN
    @5
    fveq2
    eqeq12d
    imbi2d
    @18
    @10
    wph
    @15
    c0
    @16
    wph
    cA
    cB
    cP
    vm
    vn
    vp
    smupval.a
    smupval.b
    smupval.p
    smup0
    wph
    @3
    cB
    @5
    vm
    vn
    vp
    wph
    @3
    cA
    cn0
    cA
    @2
    inss1
    smupval.a
    syl5ss
    #
    smupval.b
    @5
    eqid
    #
    smup0
    eqtr4d
    a1i
    @19
    @2
    wcel
    #
    wph
    @22
    @26
    wph
    @33
    @22
    @26
    wi
    @22
    @26
    wph
    @33
    wa
    #
    @20
    @19
    cA
    wcel
    #
    @4
    @19
    cmin
    co
    cB
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
    @21
    @38
    csad
    co
    #
    wceq
    @20
    @21
    @38
    csad
    oveq1
    @34
    @24
    @39
    @25
    @40
    @34
    cA
    cB
    cP
    vm
    vn
    @19
    vp
    wph
    cA
    cn0
    wss
    @33
    smupval.a
    adantr
    wph
    cB
    cn0
    wss
    @33
    smupval.b
    adantr
    #
    smupval.p
    @34
    @19
    @9
    cn0
    @33
    @19
    @9
    wcel
    wph
    @19
    cc0
    cN
    elfzouz
    adantl
    nn0uz
    syl6eleqr
    #
    smupp1
    @34
    @25
    @21
    @19
    @3
    wcel
    #
    @36
    wa
    #
    vn
    cn0
    crab
    #
    csad
    co
    @40
    @34
    @3
    cB
    @5
    vm
    vn
    @19
    vp
    wph
    @3
    cn0
    wss
    @33
    @31
    adantr
    @41
    @32
    @42
    smupp1
    @34
    @45
    @38
    @21
    csad
    @34
    @44
    @37
    vn
    cn0
    @34
    @43
    @35
    @36
    @33
    @43
    @35
    wb
    wph
    @43
    @35
    @33
    @19
    cA
    @2
    elin
    rbaib
    adantl
    anbi1d
    rabbidv
    oveq2d
    eqtrd
    eqeq12d
    syl5ibr
    expcom
    a2d
    fzind2
    mpcom
    wph
    @3
    cB
    @5
    vm
    vn
    cN
    cN
    vp
    @31
    smupval.b
    @32
    smupval.n
    @3
    @2
    wss
    wph
    cA
    @2
    inss2
    a1i
    wph
    cN
    cz
    wcel
    cN
    cN
    cuz
    cfv
    wcel
    wph
    cN
    smupval.n
    nn0zd
    cN
    uzid
    syl
    smupvallem
    eqtrd
end
