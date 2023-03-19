include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cn.mm"
include "cfa.mm"
include "cdvds.mm"
include "wbr.mm"
include "cv.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "imbi2d.mm"
include "cz.mm"
include "cmin.mm"
include "cmul.mm"
include "cn0.mm"
include "nnm1nn0.mm"
include "faccl.mm"
include "syl.mm"
include "nnzd.mm"
include "nnz.mm"
include "dvdsmul2.mm"
include "syl2anc.mm"
include "facnn2.mm"
include "breqtrrd.mm"
include "a1i.mm"
include "wa.mm"
include "adantl.mm"
include "elnnuz.mm"
include "uztrn.mm"
include "sylan2b.mm"
include "sylibr.mm"
include "nnnn0d.mm"
include "peano2zd.mm"
include "dvdsmultr1.mm"
include "syl3anc.mm"
include "facp1.mm"
include "sylibrd.mm"
include "ex.mm"
include "a2d.mm"
include "uzind4.mm"
include "impcom.mm"

theorem dvdsfac
  let cK: class K
  let cN: class N
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( K e. NN /\ N e. ( ZZ>= ` K ) ) -> K || ( ! ` N ) )

  proof
    cN
    cK
    cuz
    cfv
    #
    wcel
    cK
    cn
    wcel
    #
    cK
    cN
    cfa
    cfv
    #
    cdvds
    wbr
    #
    @1
    cK
    vx
    cv
    #
    cfa
    cfv
    #
    cdvds
    wbr
    #
    wi
    @1
    cK
    cK
    cfa
    cfv
    #
    cdvds
    wbr
    #
    wi
    #
    @1
    cK
    vy
    cv
    #
    cfa
    cfv
    #
    cdvds
    wbr
    #
    wi
    @1
    cK
    @10
    c1
    caddc
    co
    #
    cfa
    cfv
    #
    cdvds
    wbr
    #
    wi
    @1
    @3
    wi
    vx
    vy
    cK
    cN
    @4
    cK
    wceq
    #
    @6
    @8
    @1
    @16
    @5
    @7
    cK
    cdvds
    @4
    cK
    cfa
    fveq2
    breq2d
    imbi2d
    @4
    @10
    wceq
    #
    @6
    @12
    @1
    @17
    @5
    @11
    cK
    cdvds
    @4
    @10
    cfa
    fveq2
    breq2d
    imbi2d
    @4
    @13
    wceq
    #
    @6
    @15
    @1
    @18
    @5
    @14
    cK
    cdvds
    @4
    @13
    cfa
    fveq2
    breq2d
    imbi2d
    @4
    cN
    wceq
    #
    @6
    @3
    @1
    @19
    @5
    @2
    cK
    cdvds
    @4
    cN
    cfa
    fveq2
    breq2d
    imbi2d
    @9
    cK
    cz
    wcel
    #
    @1
    cK
    cK
    c1
    cmin
    co
    #
    cfa
    cfv
    #
    cK
    cmul
    co
    #
    @7
    cdvds
    @1
    @22
    cz
    wcel
    @20
    cK
    @23
    cdvds
    wbr
    @1
    @22
    @1
    @21
    cn0
    wcel
    @22
    cn
    wcel
    cK
    nnm1nn0
    @21
    faccl
    syl
    nnzd
    cK
    nnz
    #
    @22
    cK
    dvdsmul2
    syl2anc
    cK
    facnn2
    breqtrrd
    a1i
    @10
    @0
    wcel
    #
    @1
    @12
    @15
    @25
    @1
    @12
    @15
    wi
    @25
    @1
    wa
    #
    @12
    cK
    @11
    @13
    cmul
    co
    #
    cdvds
    wbr
    #
    @15
    @26
    @20
    @11
    cz
    wcel
    @13
    cz
    wcel
    @12
    @28
    wi
    @1
    @20
    @25
    @24
    adantl
    @26
    @11
    @26
    @10
    cn0
    wcel
    #
    @11
    cn
    wcel
    @26
    @10
    @26
    @10
    c1
    cuz
    cfv
    #
    wcel
    #
    @10
    cn
    wcel
    @1
    @25
    cK
    @30
    wcel
    @31
    cK
    elnnuz
    cK
    @10
    c1
    uztrn
    sylan2b
    @10
    elnnuz
    sylibr
    #
    nnnn0d
    #
    @10
    faccl
    syl
    nnzd
    @26
    @10
    @26
    @10
    @32
    nnzd
    peano2zd
    cK
    @11
    @13
    dvdsmultr1
    syl3anc
    @26
    @14
    @27
    cK
    cdvds
    @26
    @29
    @14
    @27
    wceq
    @33
    @10
    facp1
    syl
    breq2d
    sylibrd
    ex
    a2d
    uzind4
    impcom
end
