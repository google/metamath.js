include "c1o.mm"
include "c2o.mm"
include "cpr.mm"
include "c0.mm"
include "cop.mm"
include "ctp.mm"
include "cslt.mm"
include "csur.mm"
include "sltsolem1.mm"
include "df-no.mm"
include "df-slt.mm"
include "nosgnn0.mm"
include "soseq.mm"

theorem sltso
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y


  assert |- <s Or No

  proof
    vx
    vy
    c1o
    c2o
    cpr
    c1o
    c0
    cop
    c1o
    c2o
    cop
    c0
    c2o
    cop
    ctp
    cslt
    vf
    vg
    csur
    sltsolem1
    vf
    vx
    df-no
    vx
    vy
    vf
    vg
    df-slt
    nosgnn0
    soseq
end
