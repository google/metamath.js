include "cn0.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cbits.mm"
include "cres.mm"
include "wf1o.mm"
include "ccnv.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "csu.mm"
include "cmpt.mm"
include "wceq.mm"
include "wa.mm"
include "wtru.mm"
include "cfv.mm"
include "eqid.mm"
include "wcel.mm"
include "wss.mm"
include "bitsss.mm"
include "a1i.mm"
include "bitsfi.mm"
include "elfpw.mm"
include "sylanbrc.mm"
include "adantl.mm"
include "simprbi.mm"
include "2nn0.mm"
include "simplbi.mm"
include "sselda.mm"
include "nn0expcld.mm"
include "fsumnn0cl.mm"
include "bitsinv2.mm"
include "eqcomd.mm"
include "ad2antll.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "syl5ibrcom.mm"
include "bitsinv1.mm"
include "ad2antrl.mm"
include "sumeq1.mm"
include "impbid.mm"
include "f1ocnv2d.mm"
include "simpld.mm"
include "wb.mm"
include "cz.mm"
include "wf.mm"
include "bitsf.mm"
include "feqmptd.mm"
include "reseq1d.mm"
include "nn0ssz.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "f1oeq1.mm"
include "syl.mm"
include "mpbird.mm"
include "cnveqd.mm"
include "simprd.mm"
include "eqtrd.mm"
include "jca.mm"
include "trud.mm"

theorem bitsf1ocnv
  let vx: setvar x
  let vn: setvar n
  let vk: setvar k
  let vm: setvar m
  let cA: class A
  let vy: setvar y
  let cN: class N

  disjoint n x
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint A n
  disjoint A x
  disjoint k y
  disjoint N k
  disjoint n y
  disjoint N n
  disjoint x y
  disjoint N x
  disjoint N y
  assert |- ( ( bits |` NN0 ) : NN0 -1-1-onto-> ( ~P NN0 i^i Fin ) /\ `' ( bits |` NN0 ) = ( x e. ( ~P NN0 i^i Fin ) |-> sum_ n e. x ( 2 ^ n ) ) )

  proof
    cn0
    cn0
    cpw
    #
    cfn
    cin
    #
    cbits
    cn0
    cres
    #
    wf1o
    #
    @2
    ccnv
    #
    vx
    @1
    vx
    cv
    #
    c2
    vn
    cv
    #
    cexp
    co
    #
    vn
    csu
    #
    cmpt
    #
    wceq
    #
    wa
    wtru
    @3
    @10
    wtru
    @3
    cn0
    @1
    vk
    cn0
    vk
    cv
    #
    cbits
    cfv
    #
    cmpt
    #
    wf1o
    #
    wtru
    @14
    @13
    ccnv
    #
    @9
    wceq
    #
    wtru
    vk
    vx
    cn0
    @1
    @12
    @8
    @13
    @13
    eqid
    @11
    cn0
    wcel
    #
    @12
    @1
    wcel
    #
    wtru
    @17
    @12
    cn0
    wss
    #
    @12
    cfn
    wcel
    @18
    @19
    @17
    @11
    bitsss
    a1i
    @11
    bitsfi
    @12
    cn0
    elfpw
    sylanbrc
    adantl
    @5
    @1
    wcel
    #
    @8
    cn0
    wcel
    wtru
    @20
    @5
    @7
    vn
    @20
    @5
    cn0
    wss
    #
    @5
    cfn
    wcel
    #
    @5
    cn0
    elfpw
    #
    simprbi
    @20
    @6
    @5
    wcel
    wa
    #
    c2
    @6
    c2
    cn0
    wcel
    @24
    2nn0
    a1i
    @20
    @5
    cn0
    @6
    @20
    @21
    @22
    @23
    simplbi
    sselda
    nn0expcld
    fsumnn0cl
    adantl
    wtru
    @17
    @20
    wa
    wa
    #
    @11
    @8
    wceq
    #
    @5
    @12
    wceq
    #
    @25
    @27
    @26
    @5
    @8
    cbits
    cfv
    #
    wceq
    #
    @20
    @29
    wtru
    @17
    @20
    @28
    @5
    @5
    vn
    bitsinv2
    eqcomd
    ad2antll
    @26
    @12
    @28
    @5
    @11
    @8
    cbits
    fveq2
    eqeq2d
    syl5ibrcom
    @25
    @26
    @27
    @11
    @12
    @7
    vn
    csu
    #
    wceq
    #
    @17
    @31
    wtru
    @20
    @17
    @30
    @11
    vn
    @11
    bitsinv1
    eqcomd
    ad2antrl
    @27
    @8
    @30
    @11
    @5
    @12
    @7
    vn
    sumeq1
    eqeq2d
    syl5ibrcom
    impbid
    f1ocnv2d
    #
    simpld
    wtru
    @2
    @13
    wceq
    @3
    @14
    wb
    wtru
    @2
    vk
    cz
    @12
    cmpt
    #
    cn0
    cres
    #
    @13
    wtru
    cbits
    @33
    cn0
    wtru
    vk
    cz
    @0
    cbits
    cz
    @0
    cbits
    wf
    wtru
    bitsf
    a1i
    feqmptd
    reseq1d
    cn0
    cz
    wss
    @34
    @13
    wceq
    nn0ssz
    vk
    cz
    cn0
    @12
    resmpt
    ax-mp
    syl6eq
    #
    cn0
    @1
    @2
    @13
    f1oeq1
    syl
    mpbird
    wtru
    @4
    @15
    @9
    wtru
    @2
    @13
    @35
    cnveqd
    wtru
    @14
    @16
    @32
    simprd
    eqtrd
    jca
    trud
end
