include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "cmul.mm"
include "cdiv.mm"
include "zred.mm"
include "resubcld.mm"
include "cr.mm"
include "syl5eqel.mm"
include "remulcld.mm"
include "cc0.mm"
include "clt.mm"
include "posdifd.mm"
include "mpbid.mm"
include "syl6breqr.mm"
include "elrpd.mm"
include "iccsuble.mm"
include "recnd.mm"
include "subdird.mm"
include "pnpcand.mm"
include "eqtr4d.mm"
include "a1i.mm"
include "3brtr4d.mm"
include "lediv1dd.mm"
include "gt0ne0d.mm"
include "divcan4d.mm"
include "dividd.mm"
include "3brtr3d.mm"
include "1red.mm"
include "lesubadd2d.mm"
include "cz.mm"
include "wcel.mm"
include "wb.mm"
include "zltp1le.mm"
include "syl2anc.mm"
include "readdcld.mm"
include "letri3d.mm"
include "mpbir2and.mm"

theorem fourierdlem6
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cT: class T
  let cI: class I
  let cJ: class J
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem6.a: |- ( ph -> A e. RR )
  assume fourierdlem6.b: |- ( ph -> B e. RR )
  assume fourierdlem6.altb: |- ( ph -> A < B )
  assume fourierdlem6.t: |- T = ( B - A )
  assume fourierdlem6.5: |- ( ph -> X e. RR )
  assume fourierdlem6.i: |- ( ph -> I e. ZZ )
  assume fourierdlem6.j: |- ( ph -> J e. ZZ )
  assume fourierdlem6.iltj: |- ( ph -> I < J )
  assume fourierdlem6.iel: |- ( ph -> ( X + ( I x. T ) ) e. ( A [,] B ) )
  assume fourierdlem6.jel: |- ( ph -> ( X + ( J x. T ) ) e. ( A [,] B ) )


  assert |- ( ph -> J = ( I + 1 ) )

  proof
    wph
    cJ
    cI
    c1
    caddc
    co
    #
    wceq
    cJ
    @0
    cle
    wbr
    #
    @0
    cJ
    cle
    wbr
    #
    wph
    cJ
    cI
    cmin
    co
    #
    c1
    cle
    wbr
    @1
    wph
    @3
    cT
    cmul
    co
    #
    cT
    cdiv
    co
    cT
    cT
    cdiv
    co
    @3
    c1
    cle
    wph
    @4
    cT
    cT
    wph
    @3
    cT
    wph
    cJ
    cI
    wph
    cJ
    fourierdlem6.j
    zred
    #
    wph
    cI
    fourierdlem6.i
    zred
    #
    resubcld
    #
    wph
    cT
    cB
    cA
    cmin
    co
    #
    cr
    fourierdlem6.t
    wph
    cB
    cA
    fourierdlem6.b
    fourierdlem6.a
    resubcld
    syl5eqel
    #
    remulcld
    @9
    wph
    cT
    @9
    wph
    cc0
    @8
    cT
    clt
    wph
    cA
    cB
    clt
    wbr
    cc0
    @8
    clt
    wbr
    fourierdlem6.altb
    wph
    cA
    cB
    fourierdlem6.a
    fourierdlem6.b
    posdifd
    mpbid
    fourierdlem6.t
    syl6breqr
    #
    elrpd
    wph
    cX
    cJ
    cT
    cmul
    co
    #
    caddc
    co
    #
    cX
    cI
    cT
    cmul
    co
    #
    caddc
    co
    #
    cmin
    co
    #
    @8
    @4
    cT
    cle
    wph
    cA
    cB
    @12
    @14
    fourierdlem6.a
    fourierdlem6.b
    fourierdlem6.jel
    fourierdlem6.iel
    iccsuble
    wph
    @4
    @11
    @13
    cmin
    co
    @15
    wph
    cJ
    cI
    cT
    wph
    cJ
    @5
    recnd
    wph
    cI
    @6
    recnd
    wph
    cT
    @9
    recnd
    #
    subdird
    wph
    cX
    @11
    @13
    wph
    cX
    fourierdlem6.5
    recnd
    wph
    @11
    wph
    cJ
    cT
    @5
    @9
    remulcld
    recnd
    wph
    @13
    wph
    cI
    cT
    @6
    @9
    remulcld
    recnd
    pnpcand
    eqtr4d
    cT
    @8
    wceq
    wph
    fourierdlem6.t
    a1i
    3brtr4d
    lediv1dd
    wph
    @3
    cT
    wph
    @3
    @7
    recnd
    @16
    wph
    cT
    @10
    gt0ne0d
    #
    divcan4d
    wph
    cT
    @16
    @17
    dividd
    3brtr3d
    wph
    cJ
    cI
    c1
    @5
    @6
    wph
    1red
    #
    lesubadd2d
    mpbid
    wph
    cI
    cJ
    clt
    wbr
    #
    @2
    fourierdlem6.iltj
    wph
    cI
    cz
    wcel
    cJ
    cz
    wcel
    @19
    @2
    wb
    fourierdlem6.i
    fourierdlem6.j
    cI
    cJ
    zltp1le
    syl2anc
    mpbid
    wph
    cJ
    @0
    @5
    wph
    cI
    c1
    @6
    @18
    readdcld
    letri3d
    mpbir2and
end
