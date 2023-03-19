include "crngo.mm"
include "wcel.mm"
include "cpridl.mm"
include "cfv.mm"
include "cidl.mm"
include "c1st.mm"
include "crn.mm"
include "wne.mm"
include "cv.mm"
include "c2nd.mm"
include "co.mm"
include "wral.mm"
include "wss.mm"
include "wo.mm"
include "wi.mm"
include "wa.mm"
include "w3a.mm"
include "eqid.mm"
include "ispridl.mm"
include "3anass.mm"
include "syl6bb.mm"
include "simprbda.mm"

theorem pridlidl
  let cP: class P
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vb: setvar b


  assert |- ( ( R e. RingOps /\ P e. ( PrIdl ` R ) ) -> P e. ( Idl ` R ) )

  proof
    cR
    crngo
    wcel
    #
    cP
    cR
    cpridl
    cfv
    wcel
    #
    cP
    cR
    cidl
    cfv
    #
    wcel
    #
    cP
    cR
    c1st
    cfv
    #
    crn
    #
    wne
    #
    vx
    cv
    vy
    cv
    cR
    c2nd
    cfv
    #
    co
    cP
    wcel
    vy
    vb
    cv
    #
    wral
    vx
    va
    cv
    #
    wral
    @9
    cP
    wss
    @8
    cP
    wss
    wo
    wi
    vb
    @2
    wral
    va
    @2
    wral
    #
    wa
    #
    @0
    @1
    @3
    @6
    @10
    w3a
    @3
    @11
    wa
    vx
    vy
    cP
    cR
    @4
    @7
    @5
    va
    vb
    @4
    eqid
    @7
    eqid
    @5
    eqid
    ispridl
    @3
    @6
    @10
    3anass
    syl6bb
    simprbda
end
