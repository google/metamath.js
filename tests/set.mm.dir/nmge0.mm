include "cngp.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "c0g.mm"
include "cfv.mm"
include "cds.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cgrp.mm"
include "ngpgrp.mm"
include "eqid.mm"
include "grpidcl.mm"
include "syl.mm"
include "adantr.mm"
include "cxme.mm"
include "ngpxms.mm"
include "xmsge0.mm"
include "syl3an1.mm"
include "mpd3an3.mm"
include "wceq.mm"
include "nmval.mm"
include "adantl.mm"
include "breqtrrd.mm"

theorem nmge0
  let cA: class A
  let cG: class G
  let cN: class N
  let cX: class X
  assume nmf.x: |- X = ( Base ` G )
  assume nmf.n: |- N = ( norm ` G )


  assert |- ( ( G e. NrmGrp /\ A e. X ) -> 0 <_ ( N ` A ) )

  proof
    cG
    cngp
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    cc0
    cA
    cG
    c0g
    cfv
    #
    cG
    cds
    cfv
    #
    co
    #
    cA
    cN
    cfv
    #
    cle
    @0
    @1
    @2
    cX
    wcel
    #
    cc0
    @4
    cle
    wbr
    #
    @0
    @6
    @1
    @0
    cG
    cgrp
    wcel
    @6
    cG
    ngpgrp
    cX
    cG
    @2
    nmf.x
    @2
    eqid
    #
    grpidcl
    syl
    adantr
    @0
    cG
    cxme
    wcel
    @1
    @6
    @7
    cG
    ngpxms
    cA
    @2
    @3
    cG
    cX
    nmf.x
    @3
    eqid
    #
    xmsge0
    syl3an1
    mpd3an3
    @1
    @5
    @4
    wceq
    @0
    cA
    @3
    cN
    cG
    cX
    @2
    nmf.n
    nmf.x
    @8
    @9
    nmval
    adantl
    breqtrrd
end
