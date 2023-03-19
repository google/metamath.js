include "cc0.mm"
include "cfv.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cn.mm"
include "cv.mm"
include "cmul.mm"
include "ccos.mm"
include "csin.mm"
include "caddc.mm"
include "csu.mm"
include "wceq.mm"
include "wtru.mm"
include "cr.mm"
include "wf.mm"
include "a1i.mm"
include "wcel.mm"
include "adantl.mm"
include "cpi.mm"
include "cneg.mm"
include "cioo.mm"
include "cdm.mm"
include "cdif.mm"
include "cfn.mm"
include "cc.mm"
include "ccncf.mm"
include "cico.mm"
include "cpnf.mm"
include "cres.mm"
include "climc.mm"
include "c0.mm"
include "wne.mm"
include "cioc.mm"
include "cmnf.mm"
include "fourierd.mm"
include "trud.mm"

theorem fourier
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cT: class T
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cL: class L
  let cX: class X
  let vk: setvar k
  assume fourier.f: |- F : RR --> RR
  assume fourier.t: |- T = ( 2 x. _pi )
  assume fourier.per: |- ( x e. RR -> ( F ` ( x + T ) ) = ( F ` x ) )
  assume fourier.g: |- G = ( ( RR _D F ) |` ( -u _pi (,) _pi ) )
  assume fourier.dmdv: |- ( ( -u _pi (,) _pi ) \ dom G ) e. Fin
  assume fourier.dvcn: |- G e. ( dom G -cn-> CC )
  assume fourier.rlim: |- ( x e. ( ( -u _pi [,) _pi ) \ dom G ) -> ( ( G |` ( x (,) +oo ) ) limCC x ) =/= (/) )
  assume fourier.llim: |- ( x e. ( ( -u _pi (,] _pi ) \ dom G ) -> ( ( G |` ( -oo (,) x ) ) limCC x ) =/= (/) )
  assume fourier.x: |- X e. RR
  assume fourier.l: |- L e. ( ( F |` ( -oo (,) X ) ) limCC X )
  assume fourier.r: |- R e. ( ( F |` ( X (,) +oo ) ) limCC X )
  assume fourier.a: |- A = ( n e. NN0 |-> ( S. ( -u _pi (,) _pi ) ( ( F ` x ) x. ( cos ` ( n x. x ) ) ) _d x / _pi ) )
  assume fourier.b: |- B = ( n e. NN |-> ( S. ( -u _pi (,) _pi ) ( ( F ` x ) x. ( sin ` ( n x. x ) ) ) _d x / _pi ) )

  disjoint F n
  disjoint F x
  disjoint n x
  disjoint G x
  disjoint T x
  disjoint X n
  disjoint X x
  disjoint k x
  assert |- ( ( ( A ` 0 ) / 2 ) + sum_ n e. NN ( ( ( A ` n ) x. ( cos ` ( n x. X ) ) ) + ( ( B ` n ) x. ( sin ` ( n x. X ) ) ) ) ) = ( ( L + R ) / 2 )

  proof
    cc0
    cA
    cfv
    c2
    cdiv
    co
    cn
    vn
    cv
    #
    cA
    cfv
    @0
    cX
    cmul
    co
    #
    ccos
    cfv
    cmul
    co
    @0
    cB
    cfv
    @1
    csin
    cfv
    cmul
    co
    caddc
    co
    vn
    csu
    caddc
    co
    cL
    cR
    caddc
    co
    c2
    cdiv
    co
    wceq
    wtru
    vx
    cA
    cB
    cR
    cT
    vn
    cF
    cG
    cL
    cX
    cr
    cr
    cF
    wf
    wtru
    fourier.f
    a1i
    fourier.t
    vx
    cv
    #
    cr
    wcel
    @2
    cT
    caddc
    co
    cF
    cfv
    @2
    cF
    cfv
    wceq
    wtru
    fourier.per
    adantl
    fourier.g
    cpi
    cneg
    #
    cpi
    cioo
    co
    cG
    cdm
    #
    cdif
    cfn
    wcel
    wtru
    fourier.dmdv
    a1i
    cG
    @4
    cc
    ccncf
    co
    wcel
    wtru
    fourier.dvcn
    a1i
    @2
    @3
    cpi
    cico
    co
    @4
    cdif
    wcel
    cG
    @2
    cpnf
    cioo
    co
    cres
    @2
    climc
    co
    c0
    wne
    wtru
    fourier.rlim
    adantl
    @2
    @3
    cpi
    cioc
    co
    @4
    cdif
    wcel
    cG
    cmnf
    @2
    cioo
    co
    cres
    @2
    climc
    co
    c0
    wne
    wtru
    fourier.llim
    adantl
    cX
    cr
    wcel
    wtru
    fourier.x
    a1i
    cL
    cF
    cmnf
    cX
    cioo
    co
    cres
    cX
    climc
    co
    wcel
    wtru
    fourier.l
    a1i
    cR
    cF
    cX
    cpnf
    cioo
    co
    cres
    cX
    climc
    co
    wcel
    wtru
    fourier.r
    a1i
    fourier.a
    fourier.b
    fourierd
    trud
end
