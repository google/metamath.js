include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "csca.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cprds.mm"
include "co.mm"
include "eqid.mm"
include "pwsval.mm"
include "cvv.mm"
include "simpr.mm"
include "fvexd.mm"
include "wf.mm"
include "fconst6g.mm"
include "adantr.mm"
include "prdsgrpd.mm"
include "eqeltrd.mm"

theorem pwsgrp
  let cR: class R
  let cI: class I
  let cV: class V
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let cM: class M
  let cX: class X
  let cB: class B
  let cF: class F
  let cN: class N
  assume pwsgrp.y: |- Y = ( R ^s I )


  assert |- ( ( R e. Grp /\ I e. V ) -> Y e. Grp )

  proof
    cR
    cgrp
    wcel
    #
    cI
    cV
    wcel
    #
    wa
    #
    cY
    cR
    csca
    cfv
    #
    cI
    cR
    csn
    cxp
    #
    cprds
    co
    #
    cgrp
    cR
    @3
    cI
    cgrp
    cV
    cY
    pwsgrp.y
    @3
    eqid
    pwsval
    @2
    @4
    @3
    cI
    cvv
    cV
    @5
    @5
    eqid
    @0
    @1
    simpr
    @2
    cR
    csca
    fvexd
    @0
    cI
    cgrp
    @4
    wf
    @1
    cI
    cR
    cgrp
    fconst6g
    adantr
    prdsgrpd
    eqeltrd
end
