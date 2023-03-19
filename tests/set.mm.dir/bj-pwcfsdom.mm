include "cale.mm"
include "cfv.mm"
include "ccf.mm"
include "cv.mm"
include "char.mm"
include "cmpt.mm"
include "eqid.mm"
include "pwcfsdom.mm"

theorem bj-pwcfsdom
  let cA: class A
  let vf: setvar f
  let vy: setvar y


  assert |- ( aleph ` A ) ~< ( ( aleph ` A ) ^m ( cf ` ( aleph ` A ) ) )

  proof
    vy
    cA
    vf
    vy
    cA
    cale
    cfv
    ccf
    cfv
    vy
    cv
    vf
    cv
    cfv
    char
    cfv
    cmpt
    #
    @0
    eqid
    pwcfsdom
end
