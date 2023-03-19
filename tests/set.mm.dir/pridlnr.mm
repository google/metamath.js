include "crngo.mm"
include "wcel.mm"
include "cpridl.mm"
include "cfv.mm"
include "wne.mm"
include "cidl.mm"
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
include "3anan12.mm"
include "syl6bb.mm"
include "simprbda.mm"

theorem pridlnr
  let cP: class P
  let cR: class R
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vb: setvar b
  assume pridlnr.1: |- G = ( 1st ` R )
  assume prdilnr.2: |- X = ran G


  assert |- ( ( R e. RingOps /\ P e. ( PrIdl ` R ) ) -> P =/= X )

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
    cX
    wne
    #
    cP
    cR
    cidl
    cfv
    #
    wcel
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
    @7
    cP
    wss
    @6
    cP
    wss
    wo
    wi
    vb
    @3
    wral
    va
    @3
    wral
    #
    wa
    #
    @0
    @1
    @4
    @2
    @8
    w3a
    @2
    @9
    wa
    vx
    vy
    cP
    cR
    cG
    @5
    cX
    va
    vb
    pridlnr.1
    @5
    eqid
    prdilnr.2
    ispridl
    @4
    @2
    @8
    3anan12
    syl6bb
    simprbda
end
