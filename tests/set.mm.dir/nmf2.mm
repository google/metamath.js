include "cgrp.mm"
include "wcel.mm"
include "cme.mm"
include "cfv.mm"
include "wa.mm"
include "cr.mm"
include "wf.mm"
include "cv.mm"
include "c0g.mm"
include "co.mm"
include "cmpt.mm"
include "eqid.mm"
include "grpidcl.mm"
include "metcl.mm"
include "3comr.mm"
include "syl3an1.mm"
include "3expa.mm"
include "fmptd.mm"
include "wceq.mm"
include "nmfval2.mm"
include "adantr.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem nmf2
  let cD: class D
  let cE: class E
  let cN: class N
  let cW: class W
  let cX: class X
  let vx: setvar x
  assume nmf2.n: |- N = ( norm ` W )
  assume nmf2.x: |- X = ( Base ` W )
  assume nmf2.d: |- D = ( dist ` W )
  assume nmf2.e: |- E = ( D |` ( X X. X ) )


  assert |- ( ( W e. Grp /\ E e. ( Met ` X ) ) -> N : X --> RR )

  proof
    cW
    cgrp
    wcel
    #
    cE
    cX
    cme
    cfv
    wcel
    #
    wa
    #
    cX
    cr
    cN
    wf
    cX
    cr
    vx
    cX
    vx
    cv
    #
    cW
    c0g
    cfv
    #
    cE
    co
    #
    cmpt
    #
    wf
    @2
    vx
    cX
    @5
    cr
    @6
    @0
    @1
    @3
    cX
    wcel
    #
    @5
    cr
    wcel
    #
    @0
    @4
    cX
    wcel
    #
    @1
    @7
    @8
    cX
    cW
    @4
    nmf2.x
    @4
    eqid
    #
    grpidcl
    @1
    @7
    @9
    @8
    @3
    @4
    cE
    cX
    metcl
    3comr
    syl3an1
    3expa
    @6
    eqid
    fmptd
    @2
    cX
    cr
    cN
    @6
    @0
    cN
    @6
    wceq
    @1
    vx
    cD
    cE
    cN
    cW
    cX
    @4
    nmf2.n
    nmf2.x
    @10
    nmf2.d
    nmf2.e
    nmfval2
    adantr
    feq1d
    mpbird
end
