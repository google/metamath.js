include "cfv.mm"
include "cabs.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "abs00bd.mm"
include "0le1.mm"
include "syl6eqbr.mm"
include "wne.mm"
include "cui.mm"
include "wcel.mm"
include "adantr.mm"
include "eqid.mm"
include "dchrn0.mm"
include "biimpa.mm"
include "dchrabs.mm"
include "1le1.mm"
include "pm2.61dane.mm"

theorem dchrabs2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cG: class G
  let cN: class N
  let cX: class X
  let cZ: class Z
  assume dchrabs2.g: |- G = ( DChr ` N )
  assume dchrabs2.d: |- D = ( Base ` G )
  assume dchrabs2.z: |- Z = ( Z/nZ ` N )
  assume dchrabs2.b: |- B = ( Base ` Z )
  assume dchrabs2.x: |- ( ph -> X e. D )
  assume dchrabs2.a: |- ( ph -> A e. B )


  assert |- ( ph -> ( abs ` ( X ` A ) ) <_ 1 )

  proof
    wph
    cA
    cX
    cfv
    #
    cabs
    cfv
    #
    c1
    cle
    wbr
    @0
    cc0
    wph
    @0
    cc0
    wceq
    #
    wa
    #
    @1
    cc0
    c1
    cle
    @3
    @0
    wph
    @2
    simpr
    abs00bd
    0le1
    syl6eqbr
    wph
    @0
    cc0
    wne
    #
    wa
    #
    @1
    c1
    c1
    cle
    @5
    cA
    cD
    cZ
    cui
    cfv
    #
    cG
    cN
    cX
    cZ
    dchrabs2.g
    dchrabs2.d
    wph
    cX
    cD
    wcel
    @4
    dchrabs2.x
    adantr
    dchrabs2.z
    @6
    eqid
    #
    wph
    @4
    cA
    @6
    wcel
    wph
    cA
    cB
    cD
    @6
    cG
    cN
    cX
    cZ
    dchrabs2.g
    dchrabs2.z
    dchrabs2.d
    dchrabs2.b
    @7
    dchrabs2.x
    dchrabs2.a
    dchrn0
    biimpa
    dchrabs
    1le1
    syl6eqbr
    pm2.61dane
end
