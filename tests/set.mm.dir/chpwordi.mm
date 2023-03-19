include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "c1.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cvma.mm"
include "csu.mm"
include "cchp.mm"
include "fzfid.mm"
include "wa.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "vmacl.mm"
include "syl.mm"
include "cc0.mm"
include "vmage0.mm"
include "cuz.mm"
include "wss.mm"
include "flword2.mm"
include "fzss2.mm"
include "fsumless.mm"
include "wceq.mm"
include "chpval.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "3brtr4d.mm"

theorem chpwordi
  let cA: class A
  let cB: class B
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
  let cP: class P


  assert |- ( ( A e. RR /\ B e. RR /\ A <_ B ) -> ( psi ` A ) <_ ( psi ` B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    w3a
    #
    c1
    cA
    cfl
    cfv
    #
    cfz
    co
    #
    vn
    cv
    #
    cvma
    cfv
    #
    vn
    csu
    #
    c1
    cB
    cfl
    cfv
    #
    cfz
    co
    #
    @7
    vn
    csu
    #
    cA
    cchp
    cfv
    #
    cB
    cchp
    cfv
    #
    cle
    @3
    @10
    @7
    @5
    vn
    @3
    c1
    @9
    fzfid
    @3
    @6
    @10
    wcel
    #
    wa
    #
    @6
    cn
    wcel
    #
    @7
    cr
    wcel
    @14
    @16
    @3
    @6
    @9
    elfznn
    adantl
    #
    @6
    vmacl
    syl
    @15
    @16
    cc0
    @7
    cle
    wbr
    @17
    @6
    vmage0
    syl
    @3
    @9
    @4
    cuz
    cfv
    wcel
    @5
    @10
    wss
    cA
    cB
    flword2
    @4
    c1
    @9
    fzss2
    syl
    fsumless
    @0
    @1
    @12
    @8
    wceq
    @2
    cA
    vn
    chpval
    3ad2ant1
    @1
    @0
    @13
    @11
    wceq
    @2
    cB
    vn
    chpval
    3ad2ant2
    3brtr4d
end
