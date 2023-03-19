include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cchp.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "ce.mm"
include "c1.mm"
include "ef0.mm"
include "efchpcl.mm"
include "nnge1d.mm"
include "syl5eqbr.mm"
include "wb.mm"
include "0re.mm"
include "chpcl.mm"
include "efle.mm"
include "sylancr.mm"
include "mpbird.mm"

theorem chpge0
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cM: class M
  let cN: class N
  let cS: class S
  let cB: class B
  let cP: class P


  assert |- ( A e. RR -> 0 <_ ( psi ` A ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cchp
    cfv
    #
    cle
    wbr
    #
    cc0
    ce
    cfv
    #
    @1
    ce
    cfv
    #
    cle
    wbr
    #
    @0
    @3
    c1
    @4
    cle
    ef0
    @0
    @4
    cA
    efchpcl
    nnge1d
    syl5eqbr
    @0
    cc0
    cr
    wcel
    @1
    cr
    wcel
    @2
    @5
    wb
    0re
    cA
    chpcl
    cc0
    @1
    efle
    sylancr
    mpbird
end
