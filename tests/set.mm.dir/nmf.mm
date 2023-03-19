include "cngp.mm"
include "wcel.mm"
include "cgrp.mm"
include "cds.mm"
include "cfv.mm"
include "cxp.mm"
include "cres.mm"
include "cme.mm"
include "cr.mm"
include "wf.mm"
include "ngpgrp.mm"
include "cmt.mm"
include "ngpms.mm"
include "eqid.mm"
include "msmet.mm"
include "syl.mm"
include "nmf2.mm"
include "syl2anc.mm"

theorem nmf
  let cG: class G
  let cN: class N
  let cX: class X
  assume nmf.x: |- X = ( Base ` G )
  assume nmf.n: |- N = ( norm ` G )


  assert |- ( G e. NrmGrp -> N : X --> RR )

  proof
    cG
    cngp
    wcel
    #
    cG
    cgrp
    wcel
    cG
    cds
    cfv
    #
    cX
    cX
    cxp
    cres
    #
    cX
    cme
    cfv
    wcel
    #
    cX
    cr
    cN
    wf
    cG
    ngpgrp
    @0
    cG
    cmt
    wcel
    @3
    cG
    ngpms
    @2
    cG
    cX
    nmf.x
    @2
    eqid
    #
    msmet
    syl
    @1
    @2
    cN
    cG
    cX
    nmf.n
    nmf.x
    @1
    eqid
    @4
    nmf2
    syl2anc
end
