include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "cort.mm"
include "cfv.mm"
include "cdmd.mm"
include "wbr.mm"
include "cmd.mm"
include "wb.mm"
include "choccl.mm"
include "dmdmd.mm"
include "syl2an.mm"
include "ococ.mm"
include "breqan12d.mm"
include "bitr2d.mm"

theorem mddmd
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A MH B <-> ( _|_ ` A ) MH* ( _|_ ` B ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    wa
    cA
    cort
    cfv
    #
    cB
    cort
    cfv
    #
    cdmd
    wbr
    #
    @2
    cort
    cfv
    #
    @3
    cort
    cfv
    #
    cmd
    wbr
    #
    cA
    cB
    cmd
    wbr
    @0
    @2
    cch
    wcel
    @3
    cch
    wcel
    @4
    @7
    wb
    @1
    cA
    choccl
    cB
    choccl
    @2
    @3
    dmdmd
    syl2an
    @0
    @1
    @5
    cA
    @6
    cB
    cmd
    cA
    ococ
    cB
    ococ
    breqan12d
    bitr2d
end
