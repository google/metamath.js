include "c2.mm"
include "cz.mm"
include "wcel.mm"
include "c3.mm"
include "c4.mm"
include "ctp.mm"
include "clcmf.mm"
include "cfv.mm"
include "c1.mm"
include "cdc.mm"
include "wceq.mm"
include "2z.mm"
include "3z.mm"
include "4z.mm"
include "w3a.mm"
include "clcm.mm"
include "co.mm"
include "lcmftp.mm"
include "c6.mm"
include "lcmcom.mm"
include "3adant3.mm"
include "3lcm2e6woprm.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "6lcm4e12.mm"
include "eqtrd.mm"
include "mp3an.mm"

theorem lcmf2a3a4e12



  assert |- ( _lcm ` { 2 , 3 , 4 } ) = ; 1 2

  proof
    c2
    cz
    wcel
    #
    c3
    cz
    wcel
    #
    c4
    cz
    wcel
    #
    c2
    c3
    c4
    ctp
    clcmf
    cfv
    #
    c1
    c2
    cdc
    #
    wceq
    2z
    3z
    4z
    @0
    @1
    @2
    w3a
    #
    @3
    c2
    c3
    clcm
    co
    #
    c4
    clcm
    co
    #
    @4
    c2
    c3
    c4
    lcmftp
    @5
    @7
    c6
    c4
    clcm
    co
    @4
    @5
    @6
    c6
    c4
    clcm
    @5
    @6
    c3
    c2
    clcm
    co
    #
    c6
    @0
    @1
    @6
    @8
    wceq
    @2
    c2
    c3
    lcmcom
    3adant3
    3lcm2e6woprm
    syl6eq
    oveq1d
    6lcm4e12
    syl6eq
    eqtrd
    mp3an
end
