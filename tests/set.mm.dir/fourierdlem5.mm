include "cr.mm"
include "wcel.mm"
include "cpi.mm"
include "cneg.mm"
include "cicc.mm"
include "co.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "caddc.mm"
include "cv.mm"
include "cmul.mm"
include "csin.mm"
include "cfv.mm"
include "wa.mm"
include "simpl.mm"
include "1red.mm"
include "rehalfcld.mm"
include "readdcld.mm"
include "wss.mm"
include "pire.mm"
include "renegcli.mm"
include "iccssre.mm"
include "mp2an.mm"
include "sseli.mm"
include "adantl.mm"
include "remulcld.mm"
include "resincld.mm"
include "fmptd.mm"

theorem fourierdlem5
  let vx: setvar x
  let cS: class S
  let cX: class X
  let vk: setvar k
  assume fourierdlem5.1: |- S = ( x e. ( -u _pi [,] _pi ) |-> ( sin ` ( ( X + ( 1 / 2 ) ) x. x ) ) )

  disjoint X x
  disjoint k x
  assert |- ( X e. RR -> S : ( -u _pi [,] _pi ) --> RR )

  proof
    cX
    cr
    wcel
    #
    vx
    cpi
    cneg
    #
    cpi
    cicc
    co
    #
    cX
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    vx
    cv
    #
    cmul
    co
    #
    csin
    cfv
    cr
    cS
    @0
    @5
    @2
    wcel
    #
    wa
    #
    @6
    @8
    @4
    @5
    @8
    cX
    @3
    @0
    @7
    simpl
    @8
    c1
    @8
    1red
    rehalfcld
    readdcld
    @7
    @5
    cr
    wcel
    @0
    @2
    cr
    @5
    @1
    cr
    wcel
    cpi
    cr
    wcel
    @2
    cr
    wss
    cpi
    pire
    renegcli
    pire
    @1
    cpi
    iccssre
    mp2an
    sseli
    adantl
    remulcld
    resincld
    fourierdlem5.1
    fmptd
end
