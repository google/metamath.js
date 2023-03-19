include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wf1o.mm"
include "ccnv.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "eqid.mm"
include "grpcl.mm"
include "3expa.mm"
include "simpl.mm"
include "grpinvcl.mm"
include "jca.mm"
include "sylan.mm"
include "eqcom.mm"
include "c0g.mm"
include "grplinv.mm"
include "adantr.mm"
include "oveq1d.mm"
include "simpll.mm"
include "simplr.mm"
include "simprl.mm"
include "grpass.mm"
include "syl13anc.mm"
include "grplid.mm"
include "ad2ant2r.mm"
include "3eqtr3rd.mm"
include "eqeq2d.mm"
include "syl5bb.mm"
include "wb.mm"
include "simprr.mm"
include "adantrr.mm"
include "grplcan.mm"
include "bitrd.mm"
include "f1ocnv2d.mm"
include "grplactfval.mm"
include "adantl.mm"
include "f1oeq1.mm"
include "syl.mm"
include "cnveqd.mm"
include "oveq2.mm"
include "cbvmptv.mm"
include "syl6eq.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "mpbird.mm"

theorem grplactcnv
  let cA: class A
  let c.pl: class .+
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cI: class I
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let cB: class B
  assume grplact.1: |- F = ( g e. X |-> ( a e. X |-> ( g .+ a ) ) )
  assume grplact.2: |- X = ( Base ` G )
  assume grplact.3: |- .+ = ( +g ` G )
  assume grplactcnv.4: |- I = ( invg ` G )

  disjoint a g
  disjoint A a
  disjoint A g
  disjoint G a
  disjoint G g
  disjoint I a
  disjoint I g
  disjoint .+ a
  disjoint .+ g
  disjoint X a
  disjoint X g
  disjoint a b
  disjoint b g
  disjoint A b
  disjoint G b
  disjoint I b
  disjoint .+ b
  disjoint X b
  disjoint B a
  assert |- ( ( G e. Grp /\ A e. X ) -> ( ( F ` A ) : X -1-1-onto-> X /\ `' ( F ` A ) = ( F ` ( I ` A ) ) ) )

  proof
    cG
    cgrp
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cX
    cX
    cA
    cF
    cfv
    #
    wf1o
    #
    @3
    ccnv
    #
    cA
    cI
    cfv
    #
    cF
    cfv
    #
    wceq
    #
    wa
    cX
    cX
    va
    cX
    cA
    va
    cv
    #
    c.pl
    co
    #
    cmpt
    #
    wf1o
    #
    @11
    ccnv
    #
    vb
    cX
    @6
    vb
    cv
    #
    c.pl
    co
    #
    cmpt
    #
    wceq
    #
    wa
    @2
    va
    vb
    cX
    cX
    @10
    @15
    @11
    @11
    eqid
    @0
    @1
    @9
    cX
    wcel
    #
    @10
    cX
    wcel
    #
    cX
    c.pl
    cG
    cA
    @9
    grplact.2
    grplact.3
    grpcl
    3expa
    #
    @2
    @0
    @6
    cX
    wcel
    #
    wa
    @14
    cX
    wcel
    #
    @15
    cX
    wcel
    #
    @2
    @0
    @21
    @0
    @1
    simpl
    cX
    cG
    cI
    cA
    grplact.2
    grplactcnv.4
    grpinvcl
    #
    jca
    @0
    @21
    @22
    @23
    cX
    c.pl
    cG
    @6
    @14
    grplact.2
    grplact.3
    grpcl
    3expa
    sylan
    @2
    @18
    @22
    wa
    #
    wa
    #
    @9
    @15
    wceq
    #
    @15
    @6
    @10
    c.pl
    co
    #
    wceq
    #
    @14
    @10
    wceq
    #
    @27
    @15
    @9
    wceq
    @26
    @29
    @9
    @15
    eqcom
    @26
    @9
    @28
    @15
    @26
    @6
    cA
    c.pl
    co
    #
    @9
    c.pl
    co
    #
    cG
    c0g
    cfv
    #
    @9
    c.pl
    co
    #
    @28
    @9
    @26
    @31
    @33
    @9
    c.pl
    @2
    @31
    @33
    wceq
    @25
    cX
    c.pl
    cG
    cI
    cA
    @33
    grplact.2
    grplact.3
    @33
    eqid
    #
    grplactcnv.4
    grplinv
    adantr
    oveq1d
    @26
    @0
    @21
    @1
    @18
    @32
    @28
    wceq
    @0
    @1
    @25
    simpll
    #
    @2
    @21
    @25
    @24
    adantr
    #
    @0
    @1
    @25
    simplr
    @2
    @18
    @22
    simprl
    cX
    c.pl
    cG
    @6
    cA
    @9
    grplact.2
    grplact.3
    grpass
    syl13anc
    @0
    @18
    @34
    @9
    wceq
    @1
    @22
    cX
    c.pl
    cG
    @9
    @33
    grplact.2
    grplact.3
    @35
    grplid
    ad2ant2r
    3eqtr3rd
    eqeq2d
    syl5bb
    @26
    @0
    @22
    @19
    @21
    @29
    @30
    wb
    @36
    @2
    @18
    @22
    simprr
    @2
    @18
    @19
    @22
    @20
    adantrr
    @37
    cX
    c.pl
    cG
    @14
    @10
    @6
    grplact.2
    grplact.3
    grplcan
    syl13anc
    bitrd
    f1ocnv2d
    @2
    @4
    @12
    @8
    @17
    @2
    @3
    @11
    wceq
    #
    @4
    @12
    wb
    @1
    @38
    @0
    cA
    c.pl
    vg
    cF
    cG
    cX
    va
    grplact.1
    grplact.2
    grplactfval
    adantl
    #
    cX
    cX
    @3
    @11
    f1oeq1
    syl
    @2
    @5
    @13
    @7
    @16
    @2
    @3
    @11
    @39
    cnveqd
    @2
    @21
    @7
    @16
    wceq
    @24
    @21
    @7
    va
    cX
    @6
    @9
    c.pl
    co
    #
    cmpt
    @16
    @6
    c.pl
    vg
    cF
    cG
    cX
    va
    grplact.1
    grplact.2
    grplactfval
    va
    vb
    cX
    @40
    @15
    @9
    @14
    @6
    c.pl
    oveq2
    cbvmptv
    syl6eq
    syl
    eqeq12d
    anbi12d
    mpbird
end
