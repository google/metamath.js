include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "wf.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cpm.mm"
include "ovex.mm"
include "cvtx.mm"
include "fvex.mm"
include "eqeltri.mm"
include "simpl.mm"
include "fpmg.mm"
include "mp3an12i.mm"

theorem 0wlkonlem2
  let cP: class P
  let cG: class G
  let cN: class N
  let cV: class V
  let vk: setvar k
  assume 0wlk.v: |- V = ( Vtx ` G )


  assert |- ( ( P : ( 0 ... 0 ) --> V /\ ( P ` 0 ) = N ) -> P e. ( V ^pm ( 0 ... 0 ) ) )

  proof
    cc0
    cc0
    cfz
    co
    #
    cvv
    wcel
    cV
    cvv
    wcel
    @0
    cV
    cP
    wf
    #
    cc0
    cP
    cfv
    cN
    wceq
    #
    wa
    @1
    cP
    cV
    @0
    cpm
    co
    wcel
    cc0
    cc0
    cfz
    ovex
    cV
    cG
    cvtx
    cfv
    cvv
    0wlk.v
    cG
    cvtx
    fvex
    eqeltri
    @1
    @2
    simpl
    @0
    cV
    cP
    cvv
    cvv
    fpmg
    mp3an12i
end
