include "cngp.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cds.mm"
include "co.mm"
include "eqid.mm"
include "nmval.mm"
include "adantl.mm"
include "eqeq1d.mm"
include "wb.mm"
include "cgrp.mm"
include "ngpgrp.mm"
include "adantr.mm"
include "grpidcl.mm"
include "syl.mm"
include "cxme.mm"
include "ngpxms.mm"
include "xmseq0.mm"
include "syl3an1.mm"
include "mpd3an3.mm"
include "bitrd.mm"

theorem nmeq0
  let cA: class A
  let cG: class G
  let cN: class N
  let cX: class X
  let c.0: class .0.
  assume nmf.x: |- X = ( Base ` G )
  assume nmf.n: |- N = ( norm ` G )
  assume nmeq0.z: |- .0. = ( 0g ` G )


  assert |- ( ( G e. NrmGrp /\ A e. X ) -> ( ( N ` A ) = 0 <-> A = .0. ) )

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
    #
    cA
    cN
    cfv
    #
    cc0
    wceq
    cA
    c.0
    cG
    cds
    cfv
    #
    co
    #
    cc0
    wceq
    #
    cA
    c.0
    wceq
    #
    @2
    @3
    @5
    cc0
    @1
    @3
    @5
    wceq
    @0
    cA
    @4
    cN
    cG
    cX
    c.0
    nmf.n
    nmf.x
    nmeq0.z
    @4
    eqid
    #
    nmval
    adantl
    eqeq1d
    @0
    @1
    c.0
    cX
    wcel
    #
    @6
    @7
    wb
    #
    @2
    cG
    cgrp
    wcel
    #
    @9
    @0
    @11
    @1
    cG
    ngpgrp
    adantr
    cX
    cG
    c.0
    nmf.x
    nmeq0.z
    grpidcl
    syl
    @0
    cG
    cxme
    wcel
    @1
    @9
    @10
    cG
    ngpxms
    cA
    c.0
    @4
    cG
    cX
    nmf.x
    @8
    xmseq0
    syl3an1
    mpd3an3
    bitrd
end
