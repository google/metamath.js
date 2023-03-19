include "wf1.mm"
include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "c0g.mm"
include "cfv.mm"
include "wceq.mm"
include "crn.mm"
include "cplusg.mm"
include "cimas.mm"
include "co.mm"
include "a1i.mm"
include "cbs.mm"
include "eqidd.mm"
include "wf1o.mm"
include "wfo.mm"
include "f1f1orn.mm"
include "adantr.mm"
include "f1ofo.mm"
include "syl.mm"
include "cv.mm"
include "f1ocpbl.mm"
include "simpr.mm"
include "eqid.mm"
include "imasgrp.mm"
include "simpld.mm"

theorem imasgrpf1
  let cB: class B
  let cR: class R
  let cU: class U
  let cF: class F
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vp: setvar p
  let vq: setvar q
  assume imasgrpf1.u: |- U = ( F "s R )
  assume imasgrpf1.v: |- V = ( Base ` R )


  assert |- ( ( F : V -1-1-> B /\ R e. Grp ) -> U e. Grp )

  proof
    cV
    cB
    cF
    wf1
    #
    cR
    cgrp
    wcel
    #
    wa
    #
    cU
    cgrp
    wcel
    cR
    c0g
    cfv
    #
    cF
    cfv
    cU
    c0g
    cfv
    wceq
    @2
    cF
    crn
    #
    cR
    cplusg
    cfv
    #
    cR
    cU
    cF
    cV
    @3
    vq
    vp
    va
    vb
    cU
    cF
    cR
    cimas
    co
    wceq
    @2
    imasgrpf1.u
    a1i
    cV
    cR
    cbs
    cfv
    wceq
    @2
    imasgrpf1.v
    a1i
    @2
    @5
    eqidd
    @2
    cV
    @4
    cF
    wf1o
    #
    cV
    @4
    cF
    wfo
    @0
    @6
    @1
    cV
    cB
    cF
    f1f1orn
    adantr
    #
    cV
    @4
    cF
    f1ofo
    syl
    @2
    va
    cv
    vb
    cv
    vp
    cv
    vq
    cv
    @5
    cF
    cV
    @4
    @7
    f1ocpbl
    @0
    @1
    simpr
    @3
    eqid
    imasgrp
    simpld
end
