include "crg.mm"
include "cnzr.mm"
include "cdif.mm"
include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "0ringdif.mm"
include "simprbi.mm"

theorem 0ringbas
  let cB: class B
  let cR: class R
  let c.0: class .0.
  let vk: setvar k
  let vx: setvar x
  assume 0ringdif.b: |- B = ( Base ` R )
  assume 0ringdif.0: |- .0. = ( 0g ` R )


  assert |- ( R e. ( Ring \ NzRing ) -> B = { .0. } )

  proof
    cR
    crg
    cnzr
    cdif
    wcel
    cR
    crg
    wcel
    cB
    c.0
    csn
    wceq
    cB
    cR
    c.0
    0ringdif.b
    0ringdif.0
    0ringdif
    simprbi
end
