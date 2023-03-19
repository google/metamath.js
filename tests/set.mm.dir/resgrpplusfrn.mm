include "cgrp.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cxp.mm"
include "wfo.mm"
include "crn.mm"
include "wceq.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "grpplusfo.mm"
include "adantr.mm"
include "eqidd.mm"
include "ressbas2.mm"
include "adantl.mm"
include "sqxpeqd.mm"
include "foeq123d.mm"
include "mpbird.mm"
include "forn.mm"
include "eqcomd.mm"
include "syl.mm"

theorem resgrpplusfrn
  let cB: class B
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  assume resgrpplusfrn.b: |- B = ( Base ` G )
  assume resgrpplusfrn.h: |- H = ( G |`s S )
  assume resgrpplusfrn.o: |- F = ( +f ` H )


  assert |- ( ( H e. Grp /\ S C_ B ) -> S = ran F )

  proof
    cH
    cgrp
    wcel
    #
    cS
    cB
    wss
    #
    wa
    #
    cS
    cS
    cxp
    #
    cS
    cF
    wfo
    #
    cS
    cF
    crn
    #
    wceq
    @2
    @4
    cH
    cbs
    cfv
    #
    @6
    cxp
    #
    @6
    cF
    wfo
    #
    @0
    @8
    @1
    @6
    cF
    cH
    @6
    eqid
    resgrpplusfrn.o
    grpplusfo
    adantr
    @2
    @3
    @7
    cS
    @6
    cF
    cF
    @2
    cF
    eqidd
    @2
    cS
    @6
    @1
    cS
    @6
    wceq
    @0
    cS
    cB
    cH
    cG
    resgrpplusfrn.h
    resgrpplusfrn.b
    ressbas2
    adantl
    #
    sqxpeqd
    @9
    foeq123d
    mpbird
    @4
    @5
    cS
    @3
    cS
    cF
    forn
    eqcomd
    syl
end
