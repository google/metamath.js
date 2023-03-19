include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "ne0i.mm"
include "necon2bi.mm"
include "pm2.21d.mm"
include "ralrimi.mm"

theorem rzalf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume rzalf.1: |- F/ x A = (/)


  assert |- ( A = (/) -> A. x e. A ph )

  proof
    cA
    c0
    wceq
    #
    wph
    vx
    cA
    rzalf.1
    @0
    vx
    cv
    #
    cA
    wcel
    #
    wph
    @2
    cA
    c0
    cA
    @1
    ne0i
    necon2bi
    pm2.21d
    ralrimi
end
