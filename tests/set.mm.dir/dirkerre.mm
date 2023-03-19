include "cn.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "cfv.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "cmo.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "cdiv.mm"
include "csin.mm"
include "cif.mm"
include "dirkerval2.mm"
include "2re.mm"
include "a1i.mm"
include "nnre.mm"
include "remulcld.mm"
include "1red.mm"
include "readdcld.mm"
include "pire.mm"
include "2cnd.mm"
include "recnd.mm"
include "wne.mm"
include "2ne0.mm"
include "0re.mm"
include "pipos.mm"
include "gtneii.mm"
include "mulne0d.mm"
include "redivcld.mm"
include "ad2antrr.mm"
include "dirker2re.mm"
include "ifclda.mm"
include "eqeltrd.mm"

theorem dirkerre
  let cD: class D
  let cS: class S
  let vn: setvar n
  let cN: class N
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x
  assume dirkerre.1: |- D = ( n e. NN |-> ( s e. RR |-> if ( ( s mod ( 2 x. _pi ) ) = 0 , ( ( ( 2 x. n ) + 1 ) / ( 2 x. _pi ) ) , ( ( sin ` ( ( n + ( 1 / 2 ) ) x. s ) ) / ( ( 2 x. _pi ) x. ( sin ` ( s / 2 ) ) ) ) ) ) )

  disjoint N s
  disjoint n s
  disjoint k x
  assert |- ( ( N e. NN /\ S e. RR ) -> ( ( D ` N ) ` S ) e. RR )

  proof
    cN
    cn
    wcel
    #
    cS
    cr
    wcel
    #
    wa
    #
    cS
    cN
    cD
    cfv
    cfv
    cS
    c2
    cpi
    cmul
    co
    #
    cmo
    co
    cc0
    wceq
    #
    c2
    cN
    cmul
    co
    #
    c1
    caddc
    co
    #
    @3
    cdiv
    co
    #
    cN
    c1
    c2
    cdiv
    co
    caddc
    co
    cS
    cmul
    co
    csin
    cfv
    @3
    cS
    c2
    cdiv
    co
    csin
    cfv
    cmul
    co
    cdiv
    co
    #
    cif
    cr
    cD
    cS
    vn
    cN
    vs
    dirkerre.1
    dirkerval2
    @2
    @4
    @7
    @8
    cr
    @0
    @7
    cr
    wcel
    @1
    @4
    @0
    @6
    @3
    @0
    @5
    c1
    @0
    c2
    cN
    c2
    cr
    wcel
    @0
    2re
    a1i
    #
    cN
    nnre
    remulcld
    @0
    1red
    readdcld
    @0
    c2
    cpi
    @9
    cpi
    cr
    wcel
    @0
    pire
    a1i
    #
    remulcld
    @0
    c2
    cpi
    @0
    2cnd
    @0
    cpi
    @10
    recnd
    c2
    cc0
    wne
    @0
    2ne0
    a1i
    cpi
    cc0
    wne
    @0
    cc0
    cpi
    0re
    pipos
    gtneii
    a1i
    mulne0d
    redivcld
    ad2antrr
    cS
    cN
    dirker2re
    ifclda
    eqeltrd
end
