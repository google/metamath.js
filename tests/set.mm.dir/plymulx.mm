include "cr.mm"
include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "c0p.mm"
include "wceq.mm"
include "cidp.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "ccoe.mm"
include "cn0.mm"
include "cv.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "cc.mm"
include "wss.mm"
include "ax-resscn.mm"
include "1re.mm"
include "plyid.mm"
include "mp2an.mm"
include "plymul02.mm"
include "fveq2d.mm"
include "ax-mp.mm"
include "csn.mm"
include "cxp.mm"
include "fconstmpt.mm"
include "coe0.mm"
include "wa.mm"
include "eqidd.mm"
include "wn.mm"
include "cn.mm"
include "wne.mm"
include "elnnne0.mm"
include "df-ne.mm"
include "anbi2i.mm"
include "bitr2i.mm"
include "nnm1nn0.mm"
include "sylbi.mm"
include "eqtri.mm"
include "c0ex.mm"
include "fvmpt.mm"
include "syl.mm"
include "ifeqda.mm"
include "mpteq2ia.mm"
include "3eqtr4ri.mm"
include "eqtr4i.mm"
include "oveq1.mm"
include "simpl.mm"
include "fveq1d.mm"
include "ifeq2d.mm"
include "mpteq2dva.mm"
include "3eqtr4a.mm"
include "adantl.mm"
include "cdif.mm"
include "elsng.mm"
include "notbid.mm"
include "biimpar.mm"
include "eldifd.mm"
include "plymulx0.mm"
include "pm2.61dan.mm"

theorem plymulx
  let vn: setvar n
  let cF: class F
  let vm: setvar m

  disjoint F n
  disjoint m n
  assert |- ( F e. ( Poly ` RR ) -> ( coeff ` ( F oF x. Xp ) ) = ( n e. NN0 |-> if ( n = 0 , 0 , ( ( coeff ` F ) ` ( n - 1 ) ) ) ) )

  proof
    cF
    cr
    cply
    cfv
    #
    wcel
    #
    cF
    c0p
    wceq
    #
    cF
    cidp
    cmul
    cof
    #
    co
    #
    ccoe
    cfv
    #
    vn
    cn0
    vn
    cv
    #
    cc0
    wceq
    #
    cc0
    @6
    c1
    cmin
    co
    #
    cF
    ccoe
    cfv
    #
    cfv
    #
    cif
    #
    cmpt
    #
    wceq
    #
    @2
    @13
    @1
    @2
    c0p
    cidp
    @3
    co
    #
    ccoe
    cfv
    #
    vn
    cn0
    @7
    cc0
    @8
    c0p
    ccoe
    cfv
    #
    cfv
    #
    cif
    #
    cmpt
    #
    @5
    @12
    @15
    @16
    @19
    cidp
    @0
    wcel
    #
    @15
    @16
    wceq
    cr
    cc
    wss
    c1
    cr
    wcel
    @20
    ax-resscn
    1re
    cr
    plyid
    mp2an
    @20
    @14
    c0p
    ccoe
    cr
    cidp
    plymul02
    fveq2d
    ax-mp
    cn0
    cc0
    csn
    cxp
    #
    vn
    cn0
    cc0
    cmpt
    @16
    @19
    vn
    cn0
    cc0
    fconstmpt
    coe0
    vn
    cn0
    @18
    cc0
    @6
    cn0
    wcel
    #
    @7
    cc0
    @17
    cc0
    @22
    @7
    wa
    cc0
    eqidd
    @22
    @7
    wn
    #
    wa
    #
    @8
    cn0
    wcel
    #
    @17
    cc0
    wceq
    @24
    @6
    cn
    wcel
    #
    @25
    @26
    @22
    @6
    cc0
    wne
    #
    wa
    @24
    @6
    elnnne0
    @27
    @23
    @22
    @6
    cc0
    df-ne
    anbi2i
    bitr2i
    @6
    nnm1nn0
    sylbi
    vm
    @8
    cc0
    cc0
    cn0
    @16
    vm
    cv
    @8
    wceq
    cc0
    eqidd
    @16
    @21
    vm
    cn0
    cc0
    cmpt
    coe0
    vm
    cn0
    cc0
    fconstmpt
    eqtri
    c0ex
    fvmpt
    syl
    ifeqda
    mpteq2ia
    3eqtr4ri
    eqtr4i
    @2
    @4
    @14
    ccoe
    cF
    c0p
    cidp
    @3
    oveq1
    fveq2d
    @2
    vn
    cn0
    @11
    @18
    @2
    @22
    wa
    #
    @7
    @10
    @17
    cc0
    @28
    @8
    @9
    @16
    @28
    cF
    c0p
    ccoe
    @2
    @22
    simpl
    fveq2d
    fveq1d
    ifeq2d
    mpteq2dva
    3eqtr4a
    adantl
    @1
    @2
    wn
    #
    wa
    #
    cF
    @0
    c0p
    csn
    #
    cdif
    wcel
    @13
    @30
    cF
    @0
    @31
    @1
    @29
    simpl
    @1
    cF
    @31
    wcel
    #
    wn
    @29
    @1
    @32
    @2
    cF
    c0p
    @0
    elsng
    notbid
    biimpar
    eldifd
    vn
    cF
    plymulx0
    syl
    pm2.61dan
end
