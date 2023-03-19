include "cr.mm"
include "wss.mm"
include "wcel.mm"
include "covol.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cxr.mm"
include "cc0.mm"
include "ovolcl.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "ovolge0.mm"
include "simp3.mm"
include "xrrege0.mm"
include "syl22anc.mm"

theorem ovollecl
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vk: setvar k
  let wph: wff ph
  let cS: class S
  let cT: class T


  assert |- ( ( A C_ RR /\ B e. RR /\ ( vol* ` A ) <_ B ) -> ( vol* ` A ) e. RR )

  proof
    cA
    cr
    wss
    #
    cB
    cr
    wcel
    #
    cA
    covol
    cfv
    #
    cB
    cle
    wbr
    #
    w3a
    @2
    cxr
    wcel
    #
    @1
    cc0
    @2
    cle
    wbr
    #
    @3
    @2
    cr
    wcel
    @0
    @1
    @4
    @3
    cA
    ovolcl
    3ad2ant1
    @0
    @1
    @3
    simp2
    @0
    @1
    @5
    @3
    cA
    ovolge0
    3ad2ant1
    @0
    @1
    @3
    simp3
    @2
    cB
    xrrege0
    syl22anc
end
