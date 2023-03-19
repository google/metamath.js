include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "caddc.mm"
include "2times.mm"
include "oveq1d.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "2cn.mm"
include "2ne0.mm"
include "divcan3.mm"
include "mp3an23.mm"
include "wa.mm"
include "2cnne0.mm"
include "divdir.mm"
include "mp3an3.mm"
include "anidms.mm"
include "3eqtr3rd.mm"

theorem 2halves
  let cA: class A


  assert |- ( A e. CC -> ( ( A / 2 ) + ( A / 2 ) ) = A )

  proof
    cA
    cc
    wcel
    #
    c2
    cA
    cmul
    co
    #
    c2
    cdiv
    co
    #
    cA
    cA
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cA
    cA
    c2
    cdiv
    co
    #
    @5
    caddc
    co
    #
    @0
    @1
    @3
    c2
    cdiv
    cA
    2times
    oveq1d
    @0
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    @2
    cA
    wceq
    2cn
    2ne0
    cA
    c2
    divcan3
    mp3an23
    @0
    @4
    @6
    wceq
    #
    @0
    @0
    @7
    @8
    wa
    @9
    2cnne0
    cA
    cA
    c2
    divdir
    mp3an3
    anidms
    3eqtr3rd
end
