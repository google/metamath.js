include "cgrp.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "eqid.mm"
include "grpbn0.mm"
include "wceq.mm"
include "fveq2.mm"
include "base0.mm"
include "syl6eqr.mm"
include "necon3i.mm"
include "syl.mm"

theorem grpn0
  let cG: class G


  assert |- ( G e. Grp -> G =/= (/) )

  proof
    cG
    cgrp
    wcel
    cG
    cbs
    cfv
    #
    c0
    wne
    cG
    c0
    wne
    @0
    cG
    @0
    eqid
    grpbn0
    cG
    c0
    @0
    c0
    cG
    c0
    wceq
    @0
    c0
    cbs
    cfv
    c0
    cG
    c0
    cbs
    fveq2
    base0
    syl6eqr
    necon3i
    syl
end
