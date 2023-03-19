include "cpi.mm"
include "cneg.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "caddc.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "cmin.mm"
include "cdiv.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "0red.mm"
include "wn.mm"
include "wf.mm"
include "adantr.mm"
include "wss.mm"
include "pire.mm"
include "renegcli.mm"
include "iccssre.mm"
include "mp2an.mm"
include "sseli.mm"
include "adantl.mm"
include "readdcld.mm"
include "ffvelrnd.mm"
include "ifcld.mm"
include "ad2antrr.mm"
include "resubcld.mm"
include "wne.mm"
include "neqne.mm"
include "redivcld.mm"
include "ifclda.mm"
include "fmptd.mm"

theorem fourierdlem9
  let wph: wff ph
  let cF: class F
  let cH: class H
  let cW: class W
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem9.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem9.x: |- ( ph -> X e. RR )
  assume fourierdlem9.r: |- ( ph -> Y e. RR )
  assume fourierdlem9.w: |- ( ph -> W e. RR )
  assume fourierdlem9.h: |- H = ( s e. ( -u _pi [,] _pi ) |-> if ( s = 0 , 0 , ( ( ( F ` ( X + s ) ) - if ( 0 < s , Y , W ) ) / s ) ) )

  disjoint ph s
  disjoint k x
  assert |- ( ph -> H : ( -u _pi [,] _pi ) --> RR )

  proof
    wph
    vs
    cpi
    cneg
    #
    cpi
    cicc
    co
    #
    vs
    cv
    #
    cc0
    wceq
    #
    cc0
    cX
    @2
    caddc
    co
    #
    cF
    cfv
    #
    cc0
    @2
    clt
    wbr
    #
    cY
    cW
    cif
    #
    cmin
    co
    #
    @2
    cdiv
    co
    #
    cif
    cr
    cH
    wph
    @2
    @1
    wcel
    #
    wa
    #
    @3
    cc0
    @9
    cr
    @11
    @3
    wa
    0red
    @11
    @3
    wn
    #
    wa
    #
    @8
    @2
    @13
    @5
    @7
    @11
    @5
    cr
    wcel
    @12
    @11
    cr
    cr
    @4
    cF
    wph
    cr
    cr
    cF
    wf
    @10
    fourierdlem9.f
    adantr
    @11
    cX
    @2
    wph
    cX
    cr
    wcel
    @10
    fourierdlem9.x
    adantr
    @10
    @2
    cr
    wcel
    #
    wph
    @1
    cr
    @2
    @0
    cr
    wcel
    cpi
    cr
    wcel
    @1
    cr
    wss
    cpi
    pire
    renegcli
    pire
    @0
    cpi
    iccssre
    mp2an
    sseli
    adantl
    #
    readdcld
    ffvelrnd
    adantr
    wph
    @7
    cr
    wcel
    @10
    @12
    wph
    @6
    cY
    cW
    cr
    fourierdlem9.r
    fourierdlem9.w
    ifcld
    ad2antrr
    resubcld
    @11
    @14
    @12
    @15
    adantr
    @12
    @2
    cc0
    wne
    @11
    @2
    cc0
    neqne
    adantl
    redivcld
    ifclda
    fourierdlem9.h
    fmptd
end
