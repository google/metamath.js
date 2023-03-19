include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "wceq.mm"
include "wrel.mm"
include "wi.mm"
include "crelexp.mm"
include "co.mm"
include "cn.mm"
include "cc0.mm"
include "wo.mm"
include "wa.mm"
include "elnn0.mm"
include "cv.mm"
include "caddc.mm"
include "eqeq1.mm"
include "imbi1d.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "releqd.mm"
include "imbi12d.mm"
include "weq.mm"
include "eqid.mm"
include "pm2.27.mm"
include "ax-mp.mm"
include "adantl.mm"
include "relexp1g.mm"
include "adantr.mm"
include "mpbird.mm"
include "ccom.mm"
include "relco.mm"
include "relexpsucnnr.mm"
include "ancoms.mm"
include "mpbiri.mm"
include "a1d.mm"
include "expimpd.mm"
include "nnind.mm"
include "relexp0rel.mm"
include "simpl.mm"
include "oveq2d.mm"
include "jaoi.mm"
include "sylbi.mm"
include "3impib.mm"

theorem relexprelg
  let cR: class R
  let cN: class N
  let cV: class V
  let vn: setvar n
  let vm: setvar m


  assert |- ( ( N e. NN0 /\ R e. V /\ ( N = 1 -> Rel R ) ) -> Rel ( R ^r N ) )

  proof
    cN
    cn0
    wcel
    #
    cR
    cV
    wcel
    #
    cN
    c1
    wceq
    #
    cR
    wrel
    #
    wi
    #
    cR
    cN
    crelexp
    co
    #
    wrel
    #
    @0
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    @1
    @4
    wa
    #
    @6
    wi
    #
    cN
    elnn0
    @7
    @10
    @8
    @1
    vn
    cv
    #
    c1
    wceq
    #
    @3
    wi
    #
    wa
    #
    cR
    @11
    crelexp
    co
    #
    wrel
    #
    wi
    @1
    c1
    c1
    wceq
    #
    @3
    wi
    #
    wa
    #
    cR
    c1
    crelexp
    co
    #
    wrel
    #
    wi
    @1
    vm
    cv
    #
    c1
    wceq
    #
    @3
    wi
    #
    wa
    #
    cR
    @22
    crelexp
    co
    #
    wrel
    #
    wi
    #
    @1
    @22
    c1
    caddc
    co
    #
    c1
    wceq
    #
    @3
    wi
    #
    wa
    #
    cR
    @29
    crelexp
    co
    #
    wrel
    #
    wi
    #
    @10
    vn
    vm
    cN
    @12
    @14
    @19
    @16
    @21
    @12
    @13
    @18
    @1
    @12
    @12
    @17
    @3
    @11
    c1
    c1
    eqeq1
    imbi1d
    anbi2d
    @12
    @15
    @20
    @11
    c1
    cR
    crelexp
    oveq2
    releqd
    imbi12d
    vn
    vm
    weq
    #
    @14
    @25
    @16
    @27
    @36
    @13
    @24
    @1
    @36
    @12
    @23
    @3
    @11
    @22
    c1
    eqeq1
    imbi1d
    anbi2d
    @36
    @15
    @26
    @11
    @22
    cR
    crelexp
    oveq2
    releqd
    imbi12d
    @11
    @29
    wceq
    #
    @14
    @32
    @16
    @34
    @37
    @13
    @31
    @1
    @37
    @12
    @30
    @3
    @11
    @29
    c1
    eqeq1
    imbi1d
    anbi2d
    @37
    @15
    @33
    @11
    @29
    cR
    crelexp
    oveq2
    releqd
    imbi12d
    @11
    cN
    wceq
    #
    @14
    @9
    @16
    @6
    @38
    @13
    @4
    @1
    @38
    @12
    @2
    @3
    @11
    cN
    c1
    eqeq1
    imbi1d
    anbi2d
    @38
    @15
    @5
    @11
    cN
    cR
    crelexp
    oveq2
    releqd
    imbi12d
    @19
    @21
    @3
    @18
    @3
    @1
    @17
    @18
    @3
    wi
    c1
    eqid
    @17
    @3
    pm2.27
    ax-mp
    adantl
    @19
    @20
    cR
    @1
    @20
    cR
    wceq
    @18
    cR
    cV
    relexp1g
    adantr
    releqd
    mpbird
    @22
    cn
    wcel
    #
    @35
    @28
    @39
    @1
    @31
    @34
    @39
    @1
    wa
    #
    @34
    @31
    @40
    @34
    @26
    cR
    ccom
    #
    wrel
    @26
    cR
    relco
    @40
    @33
    @41
    @1
    @39
    @33
    @41
    wceq
    cR
    @22
    cV
    relexpsucnnr
    ancoms
    releqd
    mpbiri
    a1d
    expimpd
    a1d
    nnind
    @8
    @1
    @4
    @6
    @8
    @1
    wa
    #
    @6
    @4
    @42
    @6
    cR
    cc0
    crelexp
    co
    #
    wrel
    #
    @1
    @44
    @8
    cR
    cV
    relexp0rel
    adantl
    @42
    @5
    @43
    @42
    cN
    cc0
    cR
    crelexp
    @8
    @1
    simpl
    oveq2d
    releqd
    mpbird
    a1d
    expimpd
    jaoi
    sylbi
    3impib
end
