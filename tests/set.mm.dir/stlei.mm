include "cst.mm"
include "wcel.mm"
include "wss.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cort.mm"
include "caddc.mm"
include "co.mm"
include "chj.mm"
include "wceq.mm"
include "cch.mm"
include "csh.mm"
include "chshii.mm"
include "shococss.mm"
include "ax-mp.mm"
include "sstr2.mm"
include "mpi.mm"
include "choccli.mm"
include "pm3.2i.mm"
include "jctil.mm"
include "stj.mm"
include "syl5.mm"
include "imp.mm"
include "c1.mm"
include "chjcli.mm"
include "stle1.mm"
include "sto1i.mm"
include "breqtrrd.mm"
include "adantr.mm"
include "eqbrtrrd.mm"
include "cr.mm"
include "w3a.mm"
include "wb.mm"
include "stcl.mm"
include "3jca.mm"
include "leadd1.mm"
include "syl.mm"
include "mpbird.mm"
include "ex.mm"

theorem stlei
  let cA: class A
  let cB: class B
  let cS: class S
  assume stle.1: |- A e. CH
  assume stle.2: |- B e. CH


  assert |- ( S e. States -> ( A C_ B -> ( S ` A ) <_ ( S ` B ) ) )

  proof
    cS
    cst
    wcel
    #
    cA
    cB
    wss
    #
    cA
    cS
    cfv
    #
    cB
    cS
    cfv
    #
    cle
    wbr
    #
    @0
    @1
    wa
    #
    @4
    @2
    cB
    cort
    cfv
    #
    cS
    cfv
    #
    caddc
    co
    #
    @3
    @7
    caddc
    co
    #
    cle
    wbr
    #
    @5
    cA
    @6
    chj
    co
    #
    cS
    cfv
    #
    @8
    @9
    cle
    @0
    @1
    @12
    @8
    wceq
    #
    @1
    cA
    cch
    wcel
    #
    @6
    cch
    wcel
    #
    wa
    #
    cA
    @6
    cort
    cfv
    #
    wss
    #
    wa
    @0
    @13
    @1
    @18
    @16
    @1
    cB
    @17
    wss
    #
    @18
    cB
    csh
    wcel
    @19
    cB
    stle.2
    chshii
    cB
    shococss
    ax-mp
    cA
    cB
    @17
    sstr2
    mpi
    @14
    @15
    stle.1
    cB
    stle.2
    choccli
    #
    pm3.2i
    jctil
    cA
    @6
    cS
    stj
    syl5
    imp
    @0
    @12
    @9
    cle
    wbr
    @1
    @0
    @12
    c1
    @9
    cle
    @0
    @11
    cch
    wcel
    @12
    c1
    cle
    wbr
    cA
    @6
    stle.1
    @20
    chjcli
    @11
    cS
    stle1
    mpi
    cB
    cS
    stle.2
    sto1i
    breqtrrd
    adantr
    eqbrtrrd
    @5
    @2
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    w3a
    #
    @4
    @10
    wb
    @0
    @24
    @1
    @0
    @21
    @22
    @23
    @0
    @14
    @21
    stle.1
    cA
    cS
    stcl
    mpi
    @0
    cB
    cch
    wcel
    @22
    stle.2
    cB
    cS
    stcl
    mpi
    @0
    @15
    @23
    @20
    @6
    cS
    stcl
    mpi
    3jca
    adantr
    @2
    @3
    @7
    leadd1
    syl
    mpbird
    ex
end
