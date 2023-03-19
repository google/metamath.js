include "cpi.mm"
include "cneg.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "fourierdlem9.mm"
include "ffvelrnda.mm"
include "fourierdlem43.mm"
include "ffvelrni.mm"
include "adantl.mm"
include "remulcld.mm"
include "fmptd.mm"

theorem fourierdlem55
  let wph: wff ph
  let cU: class U
  let cF: class F
  let cH: class H
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem55.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem55.x: |- ( ph -> X e. RR )
  assume fourierdlem55.r: |- ( ph -> Y e. RR )
  assume fourierdlem55.w: |- ( ph -> W e. RR )
  assume fourierdlem55.h: |- H = ( s e. ( -u _pi [,] _pi ) |-> if ( s = 0 , 0 , ( ( ( F ` ( X + s ) ) - if ( 0 < s , Y , W ) ) / s ) ) )
  assume fourierdlem55.k: |- K = ( s e. ( -u _pi [,] _pi ) |-> if ( s = 0 , 1 , ( s / ( 2 x. ( sin ` ( s / 2 ) ) ) ) ) )
  assume fourierdlem55.u: |- U = ( s e. ( -u _pi [,] _pi ) |-> ( ( H ` s ) x. ( K ` s ) ) )

  disjoint ph s
  disjoint k x
  assert |- ( ph -> U : ( -u _pi [,] _pi ) --> RR )

  proof
    wph
    vs
    cpi
    cneg
    cpi
    cicc
    co
    #
    vs
    cv
    #
    cH
    cfv
    #
    @1
    cK
    cfv
    #
    cmul
    co
    cr
    cU
    wph
    @1
    @0
    wcel
    #
    wa
    @2
    @3
    wph
    @0
    cr
    @1
    cH
    wph
    cF
    cH
    cW
    cX
    cY
    vs
    fourierdlem55.f
    fourierdlem55.x
    fourierdlem55.r
    fourierdlem55.w
    fourierdlem55.h
    fourierdlem9
    ffvelrnda
    @4
    @3
    cr
    wcel
    wph
    @0
    cr
    @1
    cK
    cK
    vs
    fourierdlem55.k
    fourierdlem43
    ffvelrni
    adantl
    remulcld
    fourierdlem55.u
    fmptd
end
