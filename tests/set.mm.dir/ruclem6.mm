include "cn0.mm"
include "cr.mm"
include "cxp.mm"
include "cc0.mm"
include "cseq.mm"
include "wf.mm"
include "cfv.mm"
include "c1.mm"
include "cop.mm"
include "fveq1i.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "0z.mm"
include "seq1.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "ruclem4.mm"
include "syl5eqr.mm"
include "0re.mm"
include "1re.mm"
include "opelxpi.mm"
include "mp2an.mm"
include "syl6eqel.mm"
include "cv.mm"
include "wa.mm"
include "co.mm"
include "c1st.mm"
include "c2nd.mm"
include "1st2nd2.mm"
include "ad2antrl.mm"
include "oveq1d.mm"
include "caddc.mm"
include "c2.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "cn.mm"
include "adantr.mm"
include "csb.mm"
include "cmpt2.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "simprr.mm"
include "eqid.mm"
include "ruclem1.mm"
include "simp1d.mm"
include "eqeltrd.mm"
include "nn0uz.mm"
include "0zd.mm"
include "cuz.mm"
include "0p1e1.mm"
include "fveq2i.mm"
include "nnuz.mm"
include "eqtr4i.mm"
include "eleq2i.mm"
include "csn.mm"
include "cun.mm"
include "equncomi.mm"
include "wne.mm"
include "nnne0.mm"
include "necomd.mm"
include "fvunsn.mm"
include "syl.mm"
include "syl5eq.mm"
include "adantl.mm"
include "ffvelrnda.mm"
include "sylan2b.mm"
include "seqf2.mm"
include "feq1i.mm"
include "sylibr.mm"

theorem ruclem6
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let vm: setvar m
  let cF: class F
  let cG: class G
  let vw: setvar w
  let cA: class A
  let cB: class B
  let vz: setvar z
  let vn: setvar n
  let vk: setvar k
  let cM: class M
  let cN: class N
  let cS: class S
  assume ruc.1: |- ( ph -> F : NN --> RR )
  assume ruc.2: |- ( ph -> D = ( x e. ( RR X. RR ) , y e. RR |-> [_ ( ( ( 1st ` x ) + ( 2nd ` x ) ) / 2 ) / m ]_ if ( m < y , <. ( 1st ` x ) , m >. , <. ( ( m + ( 2nd ` x ) ) / 2 ) , ( 2nd ` x ) >. ) ) )
  assume ruc.4: |- C = ( { <. 0 , <. 0 , 1 >. >. } u. F )
  assume ruc.5: |- G = seq 0 ( D , C )

  disjoint m x
  disjoint m y
  disjoint x y
  disjoint F m
  disjoint F x
  disjoint F y
  disjoint G m
  disjoint G x
  disjoint G y
  disjoint m w
  disjoint w x
  disjoint w y
  disjoint A m
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint w z
  disjoint C w
  disjoint C z
  disjoint m n
  disjoint m z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint G k
  disjoint G n
  disjoint G z
  disjoint M k
  disjoint M m
  disjoint M n
  disjoint M x
  disjoint M y
  disjoint N k
  disjoint N m
  disjoint N x
  disjoint N y
  disjoint k w
  disjoint k ph
  disjoint n w
  disjoint n ph
  disjoint ph w
  disjoint ph z
  disjoint D w
  disjoint D z
  disjoint S n
  disjoint S z
  assert |- ( ph -> G : NN0 --> ( RR X. RR ) )

  proof
    wph
    cn0
    cr
    cr
    cxp
    #
    cD
    cC
    cc0
    cseq
    #
    wf
    cn0
    @0
    cG
    wf
    wph
    vz
    vw
    @0
    cr
    cD
    cC
    cc0
    cn0
    wph
    cc0
    cC
    cfv
    #
    cc0
    c1
    cop
    #
    @0
    wph
    @2
    cc0
    cG
    cfv
    #
    @3
    @4
    cc0
    @1
    cfv
    #
    @2
    cc0
    cG
    @1
    ruc.5
    fveq1i
    cc0
    cz
    wcel
    @5
    @2
    wceq
    0z
    cD
    cC
    cc0
    seq1
    ax-mp
    eqtri
    wph
    vx
    vy
    cC
    cD
    vm
    cF
    cG
    ruc.1
    ruc.2
    ruc.4
    ruc.5
    ruclem4
    syl5eqr
    cc0
    cr
    wcel
    c1
    cr
    wcel
    @3
    @0
    wcel
    0re
    1re
    cc0
    c1
    cr
    cr
    opelxpi
    mp2an
    syl6eqel
    wph
    vz
    cv
    #
    @0
    wcel
    #
    vw
    cv
    #
    cr
    wcel
    #
    wa
    #
    wa
    #
    @6
    @8
    cD
    co
    @6
    c1st
    cfv
    #
    @6
    c2nd
    cfv
    #
    cop
    #
    @8
    cD
    co
    #
    @0
    @11
    @6
    @14
    @8
    cD
    @7
    @6
    @14
    wceq
    wph
    @9
    @6
    cr
    cr
    1st2nd2
    ad2antrl
    oveq1d
    @11
    @15
    @0
    wcel
    @15
    c1st
    cfv
    #
    @12
    @13
    caddc
    co
    c2
    cdiv
    co
    #
    @8
    clt
    wbr
    #
    @12
    @17
    @13
    caddc
    co
    c2
    cdiv
    co
    cif
    wceq
    @15
    c2nd
    cfv
    #
    @18
    @17
    @13
    cif
    wceq
    @11
    vx
    vy
    @12
    @13
    cD
    vm
    cF
    @8
    @16
    @19
    wph
    cn
    cr
    cF
    wf
    @10
    ruc.1
    adantr
    wph
    cD
    vx
    vy
    @0
    cr
    vm
    vx
    cv
    #
    c1st
    cfv
    #
    @20
    c2nd
    cfv
    #
    caddc
    co
    c2
    cdiv
    co
    vm
    cv
    #
    vy
    cv
    clt
    wbr
    @21
    @23
    cop
    @23
    @22
    caddc
    co
    c2
    cdiv
    co
    @22
    cop
    cif
    csb
    cmpt2
    wceq
    @10
    ruc.2
    adantr
    @7
    @12
    cr
    wcel
    wph
    @9
    @6
    cr
    cr
    xp1st
    ad2antrl
    @7
    @13
    cr
    wcel
    wph
    @9
    @6
    cr
    cr
    xp2nd
    ad2antrl
    wph
    @7
    @9
    simprr
    @16
    eqid
    @19
    eqid
    ruclem1
    simp1d
    eqeltrd
    nn0uz
    wph
    0zd
    @6
    cc0
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    wph
    @6
    cn
    wcel
    #
    @6
    cC
    cfv
    #
    cr
    wcel
    @25
    cn
    @6
    @25
    c1
    cuz
    cfv
    cn
    @24
    c1
    cuz
    0p1e1
    fveq2i
    nnuz
    eqtr4i
    eleq2i
    wph
    @26
    wa
    @27
    @6
    cF
    cfv
    #
    cr
    @26
    @27
    @28
    wceq
    wph
    @26
    @27
    @6
    cF
    cc0
    @3
    cop
    csn
    #
    cun
    #
    cfv
    #
    @28
    @6
    cC
    @30
    cC
    @29
    cF
    ruc.4
    equncomi
    fveq1i
    @26
    cc0
    @6
    wne
    @31
    @28
    wceq
    @26
    @6
    cc0
    @6
    nnne0
    necomd
    cF
    cc0
    @3
    @6
    fvunsn
    syl
    syl5eq
    adantl
    wph
    cn
    cr
    @6
    cF
    ruc.1
    ffvelrnda
    eqeltrd
    sylan2b
    seqf2
    cn0
    @0
    cG
    @1
    ruc.5
    feq1i
    sylibr
end
