include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "w3a.mm"
include "caddc.mm"
include "cconcat.mm"
include "cmin.mm"
include "wceq.mm"
include "cz.mm"
include "wa.mm"
include "lencl.mm"
include "nn0zd.mm"
include "anim1i.mm"
include "ancomd.mm"
include "3adant2.mm"
include "fzo0addelr.mm"
include "syl.mm"
include "ccatval2.mm"
include "syld3an3.mm"
include "elfzoelz.mm"
include "3ad2ant3.mm"
include "zcnd.mm"
include "cn0.mm"
include "3ad2ant1.mm"
include "nn0cnd.mm"
include "pncand.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem ccatval3
  let cB: class B
  let cS: class S
  let cT: class T
  let cI: class I
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x


  assert |- ( ( S e. Word B /\ T e. Word B /\ I e. ( 0 ..^ ( # ` T ) ) ) -> ( ( S ++ T ) ` ( I + ( # ` S ) ) ) = ( T ` I ) )

  proof
    cS
    cB
    cword
    #
    wcel
    #
    cT
    @0
    wcel
    #
    cI
    cc0
    cT
    chash
    cfv
    #
    cfzo
    co
    wcel
    #
    w3a
    #
    cI
    cS
    chash
    cfv
    #
    caddc
    co
    #
    cS
    cT
    cconcat
    co
    cfv
    #
    @7
    @6
    cmin
    co
    #
    cT
    cfv
    #
    cI
    cT
    cfv
    @1
    @2
    @4
    @7
    @6
    @6
    @3
    caddc
    co
    cfzo
    co
    wcel
    #
    @8
    @10
    wceq
    @5
    @4
    @6
    cz
    wcel
    #
    wa
    #
    @11
    @1
    @4
    @13
    @2
    @1
    @4
    wa
    @12
    @4
    @1
    @12
    @4
    @1
    @6
    cB
    cS
    lencl
    #
    nn0zd
    anim1i
    ancomd
    3adant2
    cI
    @3
    @6
    fzo0addelr
    syl
    cB
    cS
    cT
    @7
    ccatval2
    syld3an3
    @5
    @9
    cI
    cT
    @5
    cI
    @6
    @5
    cI
    @4
    @1
    cI
    cz
    wcel
    @2
    cI
    cc0
    @3
    elfzoelz
    3ad2ant3
    zcnd
    @5
    @6
    @1
    @2
    @6
    cn0
    wcel
    @4
    @14
    3ad2ant1
    nn0cnd
    pncand
    fveq2d
    eqtrd
end
