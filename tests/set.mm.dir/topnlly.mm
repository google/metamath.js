include "ctop.mm"
include "clly.mm"
include "wceq.mm"
include "cnlly.mm"
include "toplly.mm"
include "loclly.mm"
include "mpbi.mm"

theorem topnlly
  let va: setvar a
  let vj: setvar j
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vs: setvar s
  let cA: class A
  let cV: class V
  let cX: class X
  let cJ: class J


  assert |- N-Locally Top = Top

  proof
    ctop
    clly
    ctop
    wceq
    ctop
    cnlly
    ctop
    wceq
    toplly
    ctop
    loclly
    mpbi
end
