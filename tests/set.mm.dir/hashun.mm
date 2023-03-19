include "cfn.mm"
include "wcel.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "cun.mm"
include "ccrd.mm"
include "cfv.mm"
include "cvv.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "cc0.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "coa.mm"
include "chash.mm"
include "ficardun.mm"
include "fveq2d.mm"
include "wa.mm"
include "unfi.mm"
include "eqid.mm"
include "hashgval.mm"
include "syl.mm"
include "3adant3.mm"
include "ficardom.mm"
include "hashgadd.mm"
include "syl2an.mm"
include "oveqan12d.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"

theorem hashun
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. Fin /\ B e. Fin /\ ( A i^i B ) = (/) ) -> ( # ` ( A u. B ) ) = ( ( # ` A ) + ( # ` B ) ) )

  proof
    cA
    cfn
    wcel
    #
    cB
    cfn
    wcel
    #
    cA
    cB
    cin
    c0
    wceq
    #
    w3a
    #
    cA
    cB
    cun
    #
    ccrd
    cfv
    #
    vx
    cvv
    vx
    cv
    c1
    caddc
    co
    cmpt
    cc0
    crdg
    com
    cres
    #
    cfv
    #
    cA
    ccrd
    cfv
    #
    cB
    ccrd
    cfv
    #
    coa
    co
    #
    @6
    cfv
    #
    @4
    chash
    cfv
    #
    cA
    chash
    cfv
    #
    cB
    chash
    cfv
    #
    caddc
    co
    #
    @3
    @5
    @10
    @6
    cA
    cB
    ficardun
    fveq2d
    @0
    @1
    @7
    @12
    wceq
    #
    @2
    @0
    @1
    wa
    #
    @4
    cfn
    wcel
    @16
    cA
    cB
    unfi
    vx
    @4
    @6
    @6
    eqid
    #
    hashgval
    syl
    3adant3
    @0
    @1
    @11
    @15
    wceq
    @2
    @17
    @11
    @8
    @6
    cfv
    #
    @9
    @6
    cfv
    #
    caddc
    co
    #
    @15
    @0
    @8
    com
    wcel
    @9
    com
    wcel
    @11
    @21
    wceq
    @1
    cA
    ficardom
    cB
    ficardom
    vx
    @8
    @9
    @6
    @18
    hashgadd
    syl2an
    @0
    @1
    @19
    @13
    @20
    @14
    caddc
    vx
    cA
    @6
    @18
    hashgval
    vx
    cB
    @6
    @18
    hashgval
    oveqan12d
    eqtrd
    3adant3
    3eqtr3d
end
