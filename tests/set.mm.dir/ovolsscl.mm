include "wss.mm"
include "cr.mm"
include "covol.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "sstr.mm"
include "3adant3.mm"
include "simp3.mm"
include "ovolss.mm"
include "ovollecl.mm"
include "syl3anc.mm"

theorem ovolsscl
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


  assert |- ( ( A C_ B /\ B C_ RR /\ ( vol* ` B ) e. RR ) -> ( vol* ` A ) e. RR )

  proof
    cA
    cB
    wss
    #
    cB
    cr
    wss
    #
    cB
    covol
    cfv
    #
    cr
    wcel
    #
    w3a
    cA
    cr
    wss
    #
    @3
    cA
    covol
    cfv
    #
    @2
    cle
    wbr
    #
    @5
    cr
    wcel
    @0
    @1
    @4
    @3
    cA
    cB
    cr
    sstr
    3adant3
    @0
    @1
    @3
    simp3
    @0
    @1
    @6
    @3
    cA
    cB
    ovolss
    3adant3
    cA
    @2
    ovollecl
    syl3anc
end
