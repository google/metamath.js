include "cc0.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cv.mm"
include "csu.mm"
include "wceq.mm"
include "cicc.mm"
include "cmap.mm"
include "crab.mm"
include "cop.mm"
include "csn.mm"
include "cn0.mm"
include "wcel.mm"
include "0nn0.mm"
include "k0004val.mm"
include "ax-mp.mm"
include "0p1e1.mm"
include "oveq2i.mm"
include "cz.mm"
include "1z.mm"
include "fzsn.mm"
include "eqtri.mm"
include "rabeq.mm"
include "sumeq1i.mm"
include "cc.mm"
include "wf.mm"
include "wa.mm"
include "elmapi.mm"
include "wb.mm"
include "fsn2g.mm"
include "biimpi.mm"
include "cr.mm"
include "unitssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "sseli.mm"
include "adantr.mm"
include "3syl.mm"
include "fveq2.mm"
include "sumsn.mm"
include "sylancr.mm"
include "syl5eq.mm"
include "eqeq1d.mm"
include "rabbiia.mm"
include "rabeqsn.mm"
include "cvv.mm"
include "ovex.mm"
include "1elunit.mm"
include "k0004lem3.mm"
include "mp3an.mm"
include "mpgbir.mm"

theorem k0004val0
  let vt: setvar t
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let cN: class N
  let vv: setvar v
  assume k0004.a: |- A = ( n e. NN0 |-> { t e. ( ( 0 [,] 1 ) ^m ( 1 ... ( n + 1 ) ) ) | sum_ k e. ( 1 ... ( n + 1 ) ) ( t ` k ) = 1 } )

  disjoint k t
  disjoint k n
  disjoint n t
  disjoint N k
  disjoint N t
  disjoint N n
  disjoint N v
  assert |- ( A ` 0 ) = { { <. 1 , 1 >. } }

  proof
    cc0
    cA
    cfv
    #
    c1
    cc0
    c1
    caddc
    co
    #
    cfz
    co
    #
    vk
    cv
    #
    vt
    cv
    #
    cfv
    #
    vk
    csu
    #
    c1
    wceq
    #
    vt
    cc0
    c1
    cicc
    co
    #
    @2
    cmap
    co
    #
    crab
    #
    c1
    c1
    cop
    csn
    #
    csn
    #
    cc0
    cn0
    wcel
    @0
    @10
    wceq
    0nn0
    vt
    cA
    vk
    vn
    cc0
    k0004.a
    k0004val
    ax-mp
    @10
    c1
    @4
    cfv
    #
    c1
    wceq
    #
    vt
    @8
    c1
    csn
    #
    cmap
    co
    #
    crab
    #
    @12
    @10
    @7
    vt
    @16
    crab
    #
    @17
    @9
    @16
    wceq
    @10
    @18
    wceq
    @2
    @15
    @8
    cmap
    @2
    c1
    c1
    cfz
    co
    #
    @15
    @1
    c1
    c1
    cfz
    0p1e1
    oveq2i
    c1
    cz
    wcel
    #
    @19
    @15
    wceq
    1z
    c1
    fzsn
    ax-mp
    eqtri
    #
    oveq2i
    @7
    vt
    @9
    @16
    rabeq
    ax-mp
    @7
    @14
    vt
    @16
    @4
    @16
    wcel
    #
    @6
    @13
    c1
    @22
    @6
    @15
    @5
    vk
    csu
    #
    @13
    @2
    @15
    @5
    vk
    @21
    sumeq1i
    @22
    @20
    @13
    cc
    wcel
    #
    @23
    @13
    wceq
    1z
    @22
    @15
    @8
    @4
    wf
    #
    @13
    @8
    wcel
    #
    @4
    c1
    @13
    cop
    csn
    wceq
    #
    wa
    #
    @24
    @4
    @8
    @15
    elmapi
    @25
    @28
    @20
    @25
    @28
    wb
    1z
    c1
    @8
    @4
    cz
    fsn2g
    ax-mp
    biimpi
    @26
    @24
    @27
    @8
    cc
    @13
    @8
    cr
    cc
    unitssre
    ax-resscn
    sstri
    sseli
    adantr
    3syl
    @5
    @13
    vk
    c1
    cz
    @3
    c1
    @4
    fveq2
    sumsn
    sylancr
    syl5eq
    eqeq1d
    rabbiia
    eqtri
    @17
    @12
    wceq
    @22
    @14
    wa
    @4
    @11
    wceq
    wb
    #
    vt
    @14
    vt
    @16
    @11
    rabeqsn
    @20
    @8
    cvv
    wcel
    c1
    @8
    wcel
    @29
    1z
    cc0
    c1
    cicc
    ovex
    1elunit
    c1
    @8
    c1
    cz
    @4
    cvv
    k0004lem3
    mp3an
    mpgbir
    eqtri
    eqtri
end
