include "clpir.mm"
include "wcel.mm"
include "crg.mm"
include "wceq.mm"
include "wa.mm"
include "wss.mm"
include "islpir.mm"
include "lpiss.mm"
include "biantrud.mm"
include "eqss.mm"
include "syl6rbbr.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem islpir2
  let cP: class P
  let cR: class R
  let cU: class U
  let vr: setvar r
  let va: setvar a
  let vg: setvar g
  let cB: class B
  let cK: class K
  let cI: class I
  let c.0: class .0.
  assume lpival.p: |- P = ( LPIdeal ` R )
  assume lpiss.u: |- U = ( LIdeal ` R )


  assert |- ( R e. LPIR <-> ( R e. Ring /\ U C_ P ) )

  proof
    cR
    clpir
    wcel
    cR
    crg
    wcel
    #
    cU
    cP
    wceq
    #
    wa
    @0
    cU
    cP
    wss
    #
    wa
    cP
    cR
    cU
    lpival.p
    lpiss.u
    islpir
    @0
    @1
    @2
    @0
    @2
    @2
    cP
    cU
    wss
    #
    wa
    @1
    @0
    @3
    @2
    cP
    cR
    cU
    lpival.p
    lpiss.u
    lpiss
    biantrud
    cU
    cP
    eqss
    syl6rbbr
    pm5.32i
    bitri
end
