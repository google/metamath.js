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
include "fourierdlem55.mm"
include "ffvelrnda.mm"
include "wf.mm"
include "fourierdlem5.mm"
include "syl.mm"
include "remulcld.mm"
include "fmptd.mm"

theorem fourierdlem67
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem67.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem67.x: |- ( ph -> X e. RR )
  assume fourierdlem67.y: |- ( ph -> Y e. RR )
  assume fourierdlem67.w: |- ( ph -> W e. RR )
  assume fourierdlem67.h: |- H = ( s e. ( -u _pi [,] _pi ) |-> if ( s = 0 , 0 , ( ( ( F ` ( X + s ) ) - if ( 0 < s , Y , W ) ) / s ) ) )
  assume fourierdlem67.k: |- K = ( s e. ( -u _pi [,] _pi ) |-> if ( s = 0 , 1 , ( s / ( 2 x. ( sin ` ( s / 2 ) ) ) ) ) )
  assume fourierdlem67.u: |- U = ( s e. ( -u _pi [,] _pi ) |-> ( ( H ` s ) x. ( K ` s ) ) )
  assume fourierdlem67.n: |- ( ph -> N e. RR )
  assume fourierdlem67.s: |- S = ( s e. ( -u _pi [,] _pi ) |-> ( sin ` ( ( N + ( 1 / 2 ) ) x. s ) ) )
  assume fourierdlem67.g: |- G = ( s e. ( -u _pi [,] _pi ) |-> ( ( U ` s ) x. ( S ` s ) ) )

  disjoint N s
  disjoint ph s
  disjoint k x
  assert |- ( ph -> G : ( -u _pi [,] _pi ) --> RR )

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
    cU
    cfv
    #
    @1
    cS
    cfv
    #
    cmul
    co
    cr
    cG
    wph
    @1
    @0
    wcel
    wa
    @2
    @3
    wph
    @0
    cr
    @1
    cU
    wph
    cU
    cF
    cH
    cK
    cW
    cX
    cY
    vs
    fourierdlem67.f
    fourierdlem67.x
    fourierdlem67.y
    fourierdlem67.w
    fourierdlem67.h
    fourierdlem67.k
    fourierdlem67.u
    fourierdlem55
    ffvelrnda
    wph
    @0
    cr
    @1
    cS
    wph
    cN
    cr
    wcel
    @0
    cr
    cS
    wf
    fourierdlem67.n
    vs
    cS
    cN
    fourierdlem67.s
    fourierdlem5
    syl
    ffvelrnda
    remulcld
    fourierdlem67.g
    fmptd
end
