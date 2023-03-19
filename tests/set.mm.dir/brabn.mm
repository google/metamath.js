include "chil.mm"
include "wcel.mm"
include "cbr.mm"
include "cfv.mm"
include "cnmf.mm"
include "cno.mm"
include "cr.mm"
include "branmfn.mm"
include "normcl.mm"
include "eqeltrd.mm"

theorem brabn
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vt: setvar t
  let vu: setvar u
  let cT: class T
  let cU: class U


  assert |- ( A e. ~H -> ( normfn ` ( bra ` A ) ) e. RR )

  proof
    cA
    chil
    wcel
    cA
    cbr
    cfv
    cnmf
    cfv
    cA
    cno
    cfv
    cr
    cA
    branmfn
    cA
    normcl
    eqeltrd
end
