include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "wreu.mm"
include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "riesz3i.mm"
include "cmin.mm"
include "cc0.mm"
include "wcel.mm"
include "r19.26.mm"
include "oveq12.mm"
include "adantl.mm"
include "cc.mm"
include "lnfnfi.mm"
include "ffvelrni.mm"
include "subidd.mm"
include "adantr.mm"
include "eqtr3d.mm"
include "ralimiaa.mm"
include "sylbir.mm"
include "cmv.mm"
include "hvsubcl.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "eqeq1d.mm"
include "rspcv.mm"
include "syl.mm"
include "cno.mm"
include "c2.mm"
include "cexp.mm"
include "c0v.mm"
include "wb.mm"
include "normcl.mm"
include "recnd.mm"
include "sqeq0.mm"
include "norm-i.mm"
include "bitrd.mm"
include "normsq.mm"
include "simpl.mm"
include "simpr.mm"
include "his2sub2.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "hvsubeq0.mm"
include "3bitr3d.mm"
include "sylibd.mm"
include "syl5.mm"
include "rgen2a.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "ralbidv.mm"
include "reu4.mm"
include "mpbir2an.mm"

theorem riesz4i
  let vw: setvar w
  let vv: setvar v
  let cT: class T
  let vf: setvar f
  let vn: setvar n
  let vu: setvar u
  let vx: setvar x
  assume nlelch.1: |- T e. LinFn
  assume nlelch.2: |- T e. ContFn

  disjoint v w
  disjoint T v
  disjoint T w
  disjoint f n
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint T f
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint T n
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint T u
  disjoint v x
  disjoint w x
  disjoint T x
  assert |- E! w e. ~H A. v e. ~H ( T ` v ) = ( v .ih w )

  proof
    vv
    cv
    #
    cT
    cfv
    #
    @0
    vw
    cv
    #
    csp
    co
    #
    wceq
    #
    vv
    chil
    wral
    #
    vw
    chil
    wreu
    @5
    vw
    chil
    wrex
    @5
    @1
    @0
    vu
    cv
    #
    csp
    co
    #
    wceq
    #
    vv
    chil
    wral
    #
    wa
    #
    @2
    @6
    wceq
    #
    wi
    #
    vu
    chil
    wral
    vw
    chil
    wral
    vw
    vv
    cT
    nlelch.1
    nlelch.2
    riesz3i
    @12
    vw
    vu
    chil
    @10
    @3
    @7
    cmin
    co
    #
    cc0
    wceq
    #
    vv
    chil
    wral
    #
    @2
    chil
    wcel
    #
    @6
    chil
    wcel
    #
    wa
    #
    @11
    @10
    @4
    @8
    wa
    #
    vv
    chil
    wral
    @15
    @4
    @8
    vv
    chil
    r19.26
    @19
    @14
    vv
    chil
    @0
    chil
    wcel
    #
    @19
    wa
    @1
    @1
    cmin
    co
    #
    @13
    cc0
    @19
    @21
    @13
    wceq
    @20
    @1
    @3
    @1
    @7
    cmin
    oveq12
    adantl
    @20
    @21
    cc0
    wceq
    @19
    @20
    @1
    chil
    cc
    @0
    cT
    cT
    nlelch.1
    lnfnfi
    ffvelrni
    subidd
    adantr
    eqtr3d
    ralimiaa
    sylbir
    @18
    @15
    @2
    @6
    cmv
    co
    #
    @2
    csp
    co
    #
    @22
    @6
    csp
    co
    #
    cmin
    co
    #
    cc0
    wceq
    #
    @11
    @18
    @22
    chil
    wcel
    #
    @15
    @26
    wi
    @2
    @6
    hvsubcl
    #
    @14
    @26
    vv
    @22
    chil
    @0
    @22
    wceq
    #
    @13
    @25
    cc0
    @29
    @3
    @23
    @7
    @24
    cmin
    @0
    @22
    @2
    csp
    oveq1
    @0
    @22
    @6
    csp
    oveq1
    oveq12d
    eqeq1d
    rspcv
    syl
    @18
    @22
    cno
    cfv
    #
    c2
    cexp
    co
    #
    cc0
    wceq
    #
    @22
    c0v
    wceq
    #
    @26
    @11
    @18
    @27
    @32
    @33
    wb
    @28
    @27
    @32
    @30
    cc0
    wceq
    #
    @33
    @27
    @30
    cc
    wcel
    @32
    @34
    wb
    @27
    @30
    @22
    normcl
    recnd
    @30
    sqeq0
    syl
    @22
    norm-i
    bitrd
    syl
    @18
    @31
    @25
    cc0
    @18
    @31
    @22
    @22
    csp
    co
    #
    @25
    @18
    @27
    @31
    @35
    wceq
    @28
    @22
    normsq
    syl
    @18
    @27
    @16
    @17
    @35
    @25
    wceq
    @28
    @16
    @17
    simpl
    @16
    @17
    simpr
    @22
    @2
    @6
    his2sub2
    syl3anc
    eqtrd
    eqeq1d
    @2
    @6
    hvsubeq0
    3bitr3d
    sylibd
    syl5
    rgen2a
    @5
    @9
    vw
    vu
    chil
    @11
    @4
    @8
    vv
    chil
    @11
    @3
    @7
    @1
    @2
    @6
    @0
    csp
    oveq2
    eqeq2d
    ralbidv
    reu4
    mpbir2an
end
